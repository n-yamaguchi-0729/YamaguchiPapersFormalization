/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre.lean
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
import Nyll.JacobianVarieties.Picard.IsLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_iso_pullback_of_isPullback
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_isPullback_snd_specMap_algebraOfHom
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_finiteType_algebraOfHom
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso

/-!
# Relative Picard varieties and fibre cohomology

Deduce local freeness of a pushforward line bundle from its fibre cohomology.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.IsLocallyFreeOfRank_pushforward_of_forall_fibre
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

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry.SmoothProperCurve

theorem _root_.AlgebraicGeometry.RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec
      (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (F : (pullback c t).Modules) (hF : Scheme.Modules.IsInvertible F) (n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 = n) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward
      (pullback.snd c t)).obj F) := by
  refine Scheme.Modules.isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback
    (pullback.snd c t) F n ?_
  intro y
  obtain ⟨W, hW, hyW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
    (show y ∈ (⊤ : T.Opens) from trivial)
  let := Scheme.TwoAffineOpenCover.algebraOfHom t W
  have : Algebra.FiniteType R Γ(T, W) := Scheme.TwoAffineOpenCover.finiteType_algebraOfHom t W hW
  obtain ⟨g', hcart, -⟩ := Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom
    c t W hW
  refine ⟨W, hyW, Spec (CommRingCat.of Γ(T, W)),
    pullback c (Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, W)))), hW.isoSpec.symm,
    pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, W)))), g', hcart, ?_⟩
  refine isLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType R c ε h𝔉 Γ(T, W)
    ((Scheme.Modules.pullback g').obj F) (hF.pullback g') n ?_
  intro k _ s 𝒲
  obtain ⟨φ, hφ, -, hmod⟩ := Scheme.Modules.exists_iso_pullback_of_isPullback (pullback.snd c t)
    (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, W))))) g' hW.fromSpec hcart s
  obtain ⟨𝒱, -, -, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (s ≫ hW.fromSpec))
    (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, W)))) s) φ hφ 𝒲
    (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, W)))) s
      ((Scheme.Modules.pullback g').obj F))
    (fibreModule c t (s ≫ hW.fromSpec) F) (hmod F).some
  obtain ⟨h1, h0⟩ := hfib k (s ≫ hW.fromSpec) 𝒱
  exact ⟨e1.symm.toEquiv.subsingleton, e0.finrank_eq ▸ h0⟩
end JacobianVarieties.Picard.Proofs.IsLocallyFreeOfRank_pushforward_of_forall_fibre
end ProofImplementation
