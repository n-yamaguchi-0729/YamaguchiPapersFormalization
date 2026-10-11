/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Sheaves.RelativeSectionTwist
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.FunctionFields.Infinite_setOf_isClosed_singleton
import Nyll.AlgebraicCurves.Geometry.Schemes.isReduced_of_smooth_over_field

/-!
Choose a point with prescribed image outside the support of a relative effective Cartier
divisor.
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs
namespace RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support
attribute [-instance]
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instSMulAlgEquiv
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instMulActionAlgEquiv
  AlgebraicCurve.Pic0.instSMulAlgEquiv
  AlgebraicCurve.CurveModel.isProper
  AlgebraicCurve.CurveModel.isIntegral
  AlgebraicCurve.CurveModel.smooth
attribute [-simp]
  AlgebraicCurve.Place.mk.injEq
  AlgebraicCurve.Divisor.degree_single
  AlgebraicCurve.Divisor.smul_single
  AlgebraicCurve.Place.smul_toValuationSubring
  AlgebraicCurve.Place.heightOneSpectrum_asIdeal
  AlgebraicCurve.Place.coe_algebraMap
  AlgebraicCurve.Place.ord_one
  AlgebraicCurve.Place.coe_smulRingEquiv_apply
  AlgebraicCurve.Pic0.coe_degZeroSMulHom
  AlgebraicCurve.Place.deg_smul
  AlgebraicCurve.Pic0.mk_zero
  AlgebraicCurve.Place.mk.sizeOf_spec
  AlgebraicCurve.Divisor.degree_smul
  AlgebraicCurve.Pic0.mk_add
  AlgebraicCurve.Place.ord_zero
  AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring
  AlgebraicCurve.CurveModel.mk.injEq
  AlgebraicCurve.CurveModel.mk.sizeOf_spec

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelEffCartierDiv
open _root_.AlgebraicGeometry.RelEffCartierDiv
namespace OffSupportSol
open _root_.AlgebraicGeometry.RelEffCartierDiv
open _root_.AlgebraicGeometry

theorem main
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {d : ℕ} (D : RelEffCartierDiv c d t) (x :
      T) :
    ∃ y : ↥(pullback c t), (pullback.snd c t).base y = x ∧ y ∉ D.I.support := by
  classical
  let q := pullback.snd c t
  have hbase : MorphismProperty.IsStableUnderBaseChange
      (C := Scheme.{u}) (fun {_ _} f => SmoothOfRelativeDimension 1 f) :=
    smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  have hsm1 : SmoothOfRelativeDimension 1 q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {_ _ : Scheme.{u}} f => SmoothOfRelativeDimension 1 f)
      (IsPullback.of_hasPullback c t) inferInstance
  have hsm2 : SmoothOfRelativeDimension 1 (q.fiberToSpecResidueField x) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {_ _ : Scheme.{u}} f => SmoothOfRelativeDimension 1 f)
      (IsPullback.of_hasPullback q (T.fromSpecResidueField x)) hsm1
  have hsmooth : Smooth (q.fiberToSpecResidueField x) := @SmoothOfRelativeDimension.smooth 1 _ _
    _ hsm2
  have : IsReduced (q.fiber x) := isReduced_of_smooth_over_field hsmooth
  have : IrreducibleSpace ↥(q.fiber x) := inferInstance
  have : IsIntegral (q.fiber x) := isIntegral_of_irreducibleSpace_of_isReduced _
  have hinf : Infinite ↥(q.fiber x) := by
    have h := @AlgebraicCurve.infinite_setOf_isClosed_singleton _ _ _ (q.fiberToSpecResidueField
      x) inferInstance hsm2
    have := h.to_subtype
    exact Infinite.of_injective (fun z : {y : ↥(q.fiber x) | IsClosed ({y} : Set ↥(q.fiber x))}
      => (z : ↥(q.fiber x)))
      Subtype.val_injective
  have : IsFinite (D.I.subschemeι ≫ q) := D.isFinite
  have hfin : ((D.I.subschemeι ≫ q).base ⁻¹' {x}).Finite := Scheme.Hom.finite_preimage_singleton _ x
  by_contra hcon
  push Not at hcon
  have hsub : ∀ z : ↥(q.fiber x), ∃ w : ↥(D.I.subscheme), D.I.subschemeι.base w = (q.fiberι
    x).base z := by
    intro z
    have hx : q.base ((q.fiberι x).base z) = x := by
      have : (q.fiberι x).base z ∈ q.base ⁻¹' {x} := by
        rw [← Scheme.Hom.range_fiberι]; exact ⟨z, rfl⟩
      exact this
    have hmem := hcon _ hx
    have : (q.fiberι x).base z ∈ Set.range D.I.subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hmem
    exact this
  choose w hw using hsub
  have hwS : ∀ z, w z ∈ (D.I.subschemeι ≫ q).base ⁻¹' {x} := by
    intro z
    change q.base (D.I.subschemeι.base (w z)) ∈ ({x} : Set T)
    rw [hw z]
    have : (q.fiberι x).base z ∈ q.base ⁻¹' {x} := by
      rw [← Scheme.Hom.range_fiberι]; exact ⟨z, rfl⟩
    exact this
  have : Finite ↥((D.I.subschemeι ≫ q).base ⁻¹' {x}) := hfin.to_subtype
  have hinj : Function.Injective (fun z : ↥(q.fiber x) => (⟨w z, hwS z⟩ : ↥((D.I.subschemeι ≫
    q).base ⁻¹' {x}))) := by
    intro z₁ z₂ h12
    have h' : w z₁ = w z₂ := congrArg Subtype.val h12
    have := (hw z₁).symm.trans ((congrArg (fun v => D.I.subschemeι.base v) h') ▸ (hw z₂))
    exact (q.fiberι x).isEmbedding.injective (by rw [← hw z₁, ← hw z₂, h'])
  have := Finite.of_injective _ hinj
  exact not_finite ↥(q.fiber x)

end AlgebraicGeometry.RelEffCartierDiv.OffSupportSol

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.exists_snd_apply_eq_and_notMem_support
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {d : ℕ} (D : RelEffCartierDiv c d t) (x :
      T) :
    ∃ y : ↥(pullback c t), (pullback.snd c t).base y = x ∧ y ∉ D.I.support :=
  AlgebraicGeometry.RelEffCartierDiv.OffSupportSol.main c t D x
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support
end ProofImplementation
