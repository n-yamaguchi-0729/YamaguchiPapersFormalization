/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_isIso_baseChangeHom_pushforward_of_forall_fibre.lean
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
import Nyll.AlgebraicCurves.Geometry.Sheaves.RelativeSectionTwist
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesBaseChangeHom
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_baseChangeHom_of_forall_exists_isPullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_iso_pullback_of_isPullback
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_isPullback_snd_specMap_algebraOfHom
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_finiteType_algebraOfHom
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_FiniteMapData_exists_baseChange
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_FiniteMapData_finite_H0_H1_sectionsOf

/-!
# Is Iso base Change Hom pushforward of forall fibre
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.IsIso_baseChangeHom_pushforward_of_forall_fibre
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

namespace PFBCSketch

variable {R : Type u} [CommRing R]

theorem isPullback_baseChangeSnd {C T T' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    IsPullback (baseChangeSnd c ψ) (pullback.snd c t') (pullback.snd c t) ψ.1 := by
  refine IsPullback.of_right (h₁₂ := pullback.fst c t) (v₁₃ := c) (h₂₂ := t) ?_
    (RelPicard.BaseChange.baseChangeSnd_snd' (cc := c) (ψ := ψ)) (IsPullback.of_hasPullback c t)
  rw [RelPicard.BaseChange.baseChangeSnd_fst' (cc := c) (ψ := ψ), ψ.2]
  exact IsPullback.of_hasPullback c t'

theorem fromSpec_comp_eq_specMap {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (W : T.Opens)
    (hW : IsAffineOpen W) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom t W
    hW.fromSpec ≫ t = Scheme.TwoAffineOpenCover.specMap R Γ(T, W) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom t W
  have h := IsAffineOpen.SpecMap_appLE_fromSpec t (isAffineOpen_top _) hW (le_top (a := W))
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  change _ = Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (.of R)).inv ≫ t.appLE ⊤ W le_top).hom)
  rw [CommRingCat.ofHom_hom]
  exact h.symm

end PFBCSketch

open PFBCSketch in
theorem _root_.AlgebraicGeometry.RelPicard.isIso_baseChangeHom_pushforward_of_forall_fibre
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of
      R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
      [LocallyOfFiniteType t]
    (ψ : SchemeHomOver t' t) (F : (pullback c t).Modules) (hF : Scheme.Modules.IsInvertible F) (n :
      ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 = n) :
    IsIso (Scheme.Modules.baseChangeHom
      (RelPicard.BaseChange.baseChangeSnd_snd' (cc := c) (ψ := ψ)) F) := by
  have hcart := isPullback_baseChangeSnd c ψ
  refine Scheme.Modules.isIso_baseChangeHom_of_forall_exists_isPullback hcart F ?_
  intro y
  obtain ⟨W, hW, hyW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
    (show ψ.1.base y ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨W', hW', hyW', hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T'.isBasis_affineOpens
    (show y ∈ ψ.1 ⁻¹ᵁ W from hyW)
  let := Scheme.TwoAffineOpenCover.algebraOfHom t W
  let := Scheme.TwoAffineOpenCover.algebraOfHom t' W'
  let algW : Algebra Γ(T, W) Γ(T', W') := (ψ.1.appLE W W' hle).hom.toAlgebra
  have : Algebra.FiniteType R Γ(T, W) := Scheme.TwoAffineOpenCover.finiteType_algebraOfHom t W hW
  have : IsNoetherianRing Γ(T, W) := Algebra.FiniteType.isNoetherianRing R Γ(T, W)
  obtain ⟨u, hu, -⟩ := Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom c t W hW
  have hφ' : hW'.fromSpec ≫ ψ.1 = Scheme.TwoAffineOpenCover.specMap Γ(T, W) Γ(T', W') ≫ hW.fromSpec
    := by
    change _ = Spec.map (CommRingCat.ofHom (ψ.1.appLE W W' hle).hom) ≫ hW.fromSpec
    rw [CommRingCat.ofHom_hom]
    exact (IsAffineOpen.SpecMap_appLE_fromSpec ψ.1 hW hW' hle).symm
  have hφ : (hW'.isoSpec.symm.hom ≫ Scheme.Opens.ι W') ≫ ψ.1 =
      Scheme.TwoAffineOpenCover.specMap Γ(T, W) Γ(T', W') ≫ hW.isoSpec.symm.hom ≫ Scheme.Opens.ι W
        := by
    rw [Iso.symm_hom, Iso.symm_hom, IsAffineOpen.isoSpec_inv_ι (hU := hW'),
      IsAffineOpen.isoSpec_inv_ι (hU := hW)]
    exact hφ'
  have hφR : Scheme.TwoAffineOpenCover.specMap Γ(T, W) Γ(T', W') ≫
    Scheme.TwoAffineOpenCover.specMap R Γ(T, W) =
      Scheme.TwoAffineOpenCover.specMap R Γ(T', W') := by
    rw [← fromSpec_comp_eq_specMap t W hW, ← fromSpec_comp_eq_specMap t' W' hW', ← Category.assoc,
      ← hφ',
      Category.assoc, ψ.2]
  let ψW : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R Γ(T', W'))
      (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)) :=
    ⟨Scheme.TwoAffineOpenCover.specMap Γ(T, W) Γ(T', W'), hφR⟩
  have hv : IsPullback (baseChangeSnd c ψW) (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
    Γ(T', W')))
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)))
      (Scheme.TwoAffineOpenCover.specMap Γ(T, W) Γ(T', W')) :=
    isPullback_baseChangeSnd c ψW
  refine ⟨W, W', hyW', Spec (CommRingCat.of Γ(T, W)), Spec (CommRingCat.of Γ(T', W')),
    pullback c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)),
    pullback c (Scheme.TwoAffineOpenCover.specMap R Γ(T', W')), hW.isoSpec.symm, hW'.isoSpec.symm,
    Scheme.TwoAffineOpenCover.specMap Γ(T, W) Γ(T', W'), hφ,
    pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)), u, hu,
    pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T', W')), baseChangeSnd c ψW, hv, ?_⟩
  have : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have : Flat (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) := inferInstance
  obtain ⟨𝔉, -⟩ := h𝔉 0
  obtain ⟨𝔉A, -, -, -, -⟩ := 𝔉.exists_baseChange Γ(T, W)
  have hFu : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback u).obj F) := hF.pullback u
  have hfin := 𝔉A.finite_H0_H1_sectionsOf ((Scheme.Modules.pullback u).obj F)
    hFu.exists_trivialization
  refine Scheme.Modules.isIso_baseChangeHom_of_twoAffineOpenCover
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) 𝔉A.twoAffineOpenCover
    ((Scheme.Modules.pullback u).obj F) hFu.exists_trivialization hfin ?_ Γ(T', W')
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T', W'))) (baseChangeSnd c ψW) hv
  intro K _ _
  obtain ⟨θ, hθ, -, hmod⟩ := Scheme.Modules.exists_iso_pullback_of_isPullback (pullback.snd c t)
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) u hW.fromSpec hu
    (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K)
  obtain ⟨𝒱, -, -, -, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K ≫ hW.fromSpec))
    (fibreAt c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)) (Scheme.TwoAffineOpenCover.specMap
      Γ(T, W) K)) θ hθ
    (𝔉A.twoAffineOpenCover.pullback (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)))
      K)
    (fibreModule c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)) (Scheme.TwoAffineOpenCover.specMap
      Γ(T, W) K)
      ((Scheme.Modules.pullback u).obj F))
    (fibreModule c t (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K ≫ hW.fromSpec) F) (hmod F).some
  obtain ⟨h1, -⟩ := hfib K (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K ≫ hW.fromSpec) 𝒱
  exact e1.symm.toEquiv.subsingleton
end JacobianVarieties.Picard.Proofs.IsIso_baseChangeHom_pushforward_of_forall_fibre
end ProofImplementation
