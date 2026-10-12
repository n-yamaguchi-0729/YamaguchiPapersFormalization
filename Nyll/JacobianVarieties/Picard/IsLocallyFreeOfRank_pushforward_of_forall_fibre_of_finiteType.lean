/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_FiniteMapData_exists_baseChange
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_FiniteMapData_finite_H0_H1_sectionsOf

/-!
# Relative Picard varieties and fibre cohomology

Use finite-type base change and fibre cohomology to obtain a pushforward module of constant rank.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs
namespace IsLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry.SmoothProperCurve

theorem
  _root_.AlgebraicGeometry.RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec
      (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (F : (pullback c (Spec.map (CommRingCat.ofHom (algebraMap R A)))).Modules)
    (hF : Scheme.Modules.IsInvertible F) (n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A))
      (𝒲 : (pullback (pullback.snd c (Spec.map (CommRingCat.ofHom
        (algebraMap R A)))) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A))) s)
        (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A))) s F)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A))) s)
          (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A))) s F)).H0 = n) :
    Scheme.Modules.IsLocallyFreeOfRank n
      ((Scheme.Modules.pushforward (pullback.snd c (Spec.map (CommRingCat.ofHom
        (algebraMap R A))))).obj F) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have : Flat (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R A)))) := inferInstance
  obtain ⟨𝔉, -⟩ := h𝔉 0
  obtain ⟨𝔉A, -, -, -, -⟩ := 𝔉.exists_baseChange A
  have hfin := 𝔉A.finite_H0_H1_sectionsOf F hF.exists_trivialization
  exact Scheme.Modules.isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover
    (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R A)))) 𝔉A.twoAffineOpenCover F
    hF.exists_trivialization hfin n
    (fun K _ _ => hfib K (Scheme.TwoAffineOpenCover.specMap A K)
      (𝔉A.twoAffineOpenCover.pullback (pullback.snd c (Spec.map (CommRingCat.ofHom
        (algebraMap R A)))) K))
end IsLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType
end JacobianVarieties.Picard.Proofs
end ProofImplementation

attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
