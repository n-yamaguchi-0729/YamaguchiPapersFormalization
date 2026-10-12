/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Picard.Exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_subsingleton_H1
import Nyll.JacobianVarieties.Picard.Exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff

/-!
# Relative Picard varieties and fibre cohomology

Transfer vanishing of first cohomology from a residue-field chart to the corresponding fibre.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs
namespace Subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart
attribute [-instance] AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.SmoothProperCurve

theorem
  _root_.AlgebraicGeometry.RelPicard.subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules) (hM :
      Scheme.Modules.IsInvertible M)
    {A : Type u} [CommRing A] (j : Spec (CommRingCat.of A) ⟶ T) [IsOpenImmersion j]
    {CA : Scheme.{u}} (πA : CA ⟶ Spec (CommRingCat.of A)) (g' : CA ⟶ pullback c t)
    (hcart : IsPullback g' πA (pullback.snd c t) j)
    (𝒱 : CA.TwoAffineOpenCover) (𝔭 : PrimeSpectrum A)
    (hO : Subsingleton ((𝒱.pullback πA 𝔭.asIdeal.ResidueField).sectionsOf
            (pullback.snd πA (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))
            ((Scheme.Modules.pullback (pullback.fst πA (Scheme.TwoAffineOpenCover.specMap A
              𝔭.asIdeal.ResidueField))).obj
              ((Scheme.Modules.pullback g').obj M))).H1)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (hs : s.base (IsLocalRing.closedPoint k) = j.base 𝔭)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 := by
  classical
  set K₀ : Type u := 𝔭.asIdeal.ResidueField with hK₀
  set s₁ : Spec (CommRingCat.of K₀) ⟶ T := Scheme.TwoAffineOpenCover.specMap A K₀ ≫ j with hs₁def
  have hcart₁ : IsPullback (pullback.fst πA (Scheme.TwoAffineOpenCover.specMap A K₀) ≫ g')
      (pullback.snd πA (Scheme.TwoAffineOpenCover.specMap A K₀)) (pullback.snd c t) s₁ :=
    (IsPullback.of_hasPullback πA (Scheme.TwoAffineOpenCover.specMap A K₀)).paste_horiz hcart
  obtain ⟨𝒲₁, -, ⟨l₁⟩⟩ := exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback c
    t M s₁
    (pullback.snd πA (Scheme.TwoAffineOpenCover.specMap A K₀))
    (pullback.fst πA (Scheme.TwoAffineOpenCover.specMap A K₀) ≫ g') hcart₁
    ((Scheme.Modules.pullback (pullback.fst πA (Scheme.TwoAffineOpenCover.specMap A K₀))).obj
      ((Scheme.Modules.pullback g').obj M))
    ((Scheme.Modules.pullbackComp (pullback.fst πA (Scheme.TwoAffineOpenCover.specMap A K₀))
      g').app M)
    (𝒱.pullback πA K₀)
  have h₁ : Subsingleton (𝒲₁.sectionsOf (fibreAt c t s₁) (fibreModule c t s₁ M)).H1 :=
    l₁.symm.toEquiv.subsingleton
  have hall : ∀ {k' : Type u} [Field k'] (s' : Spec (CommRingCat.of k') ⟶ T)
      (𝒲a 𝒲b : (pullback (pullback.snd c t) s').TwoAffineOpenCover),
      Subsingleton (𝒲b.sectionsOf (fibreAt c t s') (fibreModule c t s' M)).H1 →
        Subsingleton (𝒲a.sectionsOf (fibreAt c t s') (fibreModule c t s' M)).H1 := by
    intro k' _ s' 𝒲a 𝒲b h
    have hsep : IsSeparated (fibreAt c t s') := by unfold fibreAt; infer_instance
    exact @Scheme.TwoAffineOpenCover.subsingleton_H1_sectionsOf_of_subsingleton_H1
      k' inferInstance _ (fibreAt c t s') hsep (fibreModule c t s' M)
      (hM.pullback _).exists_trivialization 𝒲a 𝒲b h
  obtain ⟨s', hs'⟩ : ∃ s' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A), s' ≫ j = s := by
    refine ⟨IsOpenImmersion.lift j s ?_, IsOpenImmersion.lift_fac j s _⟩
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint k), hs]
    exact ⟨𝔭, rfl⟩
  subst hs'
  obtain ⟨φ, rfl⟩ : ∃ φ : CommRingCat.of A ⟶ CommRingCat.of k, Spec.map φ = s' :=
    ⟨Spec.preimage s', Spec.map_preimage s'⟩
  have hpt : (Spec.map φ).base (IsLocalRing.closedPoint k) = 𝔭 := by
    apply j.isOpenEmbedding.injective
    change j.base ((Spec.map φ).base (IsLocalRing.closedPoint k)) = j.base 𝔭 at hs
    exact hs
  have hker : RingHom.ker φ.hom = 𝔭.asIdeal := by
    have h1 := congrArg PrimeSpectrum.asIdeal hpt
    have hmax : (IsLocalRing.closedPoint k).asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.closedPoint k).isPrime.ne_top
    have h2 : ((Spec.map φ).base (IsLocalRing.closedPoint k)).asIdeal =
        Ideal.comap φ.hom (IsLocalRing.closedPoint k).asIdeal := rfl
    rw [h2, hmax] at h1
    exact h1
  have hφ𝔭 : ∀ a ∈ 𝔭.asIdeal, φ.hom a = 0 := fun a ha => by
    rw [← RingHom.mem_ker, hker]; exact ha
  set φbar : A ⧸ 𝔭.asIdeal →+* k := Ideal.Quotient.lift 𝔭.asIdeal φ.hom hφ𝔭 with hφbar
  have hinj : Function.Injective φbar := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hφbar, Ideal.Quotient.lift_mk] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hker ▸ (RingHom.mem_ker.mpr ha))
  set ψ : K₀ →+* k := IsFractionRing.lift (A := A ⧸ 𝔭.asIdeal) (K := K₀) (g := φbar) hinj with hψ
  let _ : Algebra K₀ k := ψ.toAlgebra
  have hφfac : φ = CommRingCat.ofHom ((algebraMap K₀ k).comp (algebraMap A K₀)) := by
    ext a
    change φ.hom a = ψ ((algebraMap A K₀) a)
    rw [hψ, IsScalarTower.algebraMap_apply A (A ⧸ 𝔭.asIdeal) K₀, IsFractionRing.lift_algebraMap,
      hφbar, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.lift_mk]
  have h : Spec.map φ ≫ j = Scheme.TwoAffineOpenCover.specMap K₀ k ≫ s₁ := by
    rw [hs₁def, ← Category.assoc, hφfac, CommRingCat.ofHom_comp, Spec.map_comp]
  obtain ⟨𝒲', -, hiff⟩ := exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
    c t M hM s₁ 𝒲₁ k
  have h' := hiff.mpr h₁
  clear hs hpt
  revert 𝒲
  rw [h]
  intro 𝒲
  exact hall _ 𝒲 𝒲' h'
end Subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart
end JacobianVarieties.Picard.Proofs
end ProofImplementation
