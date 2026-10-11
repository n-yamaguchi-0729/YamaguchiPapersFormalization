/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_pullback_stageHom_equiv_lineBundle_appLE.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Geometry.Picard.StageHom
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial

/-!
# Scheme Two Affine Open Cover exists sections Of pullback stage Hom equiv line Bundle app
LE
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_TwoAffineOpenCover_exists_sectionsOf_pullback_stageHom_equiv_lineBundle_appLE
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp] AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec
  GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply
  GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec
  NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe
  GoodReductionJacobian.RelativeGroupLaw.mk.injEq
  NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom
  NeronModelInfra.schemeHomOverToOverHom_left
  NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct

noncomputable section


namespace P2mTJ2stage

section Free

variable {B : Type u} [CommRing B] {M : Type u} [AddCommGroup M] [Module B M]

theorem linearEquiv_symm_apply_eq_smul (e : M ≃ₗ[B] B) (b : B) : e.symm b = b • e.symm 1 := by
  rw [← map_smul, smul_eq_mul, mul_one]

end Free

section Main

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of
  R))
  (A₀ A' : Type u) [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A']
    [IsScalarTower R A₀ A']

local notation "σst" =>
  RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))
local notation "c₀" => Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)
local notation "c'" => Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A')
local notation "𝒱₀" => Scheme.TwoAffineOpenCover.pullback 𝒱 c A₀
local notation "𝒱'" => Scheme.TwoAffineOpenCover.pullback 𝒱 c A'
local notation "𝒰₀" => Scheme.TwoAffineOpenCover.cover (Scheme.TwoAffineOpenCover.pullback 𝒱 c A₀)
  (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))
local notation "𝒰'" => Scheme.TwoAffineOpenCover.cover (Scheme.TwoAffineOpenCover.pullback 𝒱 c A')
  (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))
local notation "h0≤" => Eq.ge (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c
  (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))
local notation "h1≤" => Eq.ge (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c
  (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))
local notation "h01≤" => Eq.ge (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c
  (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))

variable (L : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A₀)).Modules)
  (hL : Scheme.Modules.IsInvertible L)
  (t : ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
    A₀))).A01ˣ)
  (e0 : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
    A₀)) L).M0
    ≃ₗ[((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
      A₀))).A0]
    ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A0)
  (e1 : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
    A₀)) L).M1
    ≃ₗ[((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
      A₀))).A1]
    ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A1)
  (e01 : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
    A₀)) L).M01
    ≃ₗ[((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
      A₀))).A01]
    ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A01)
  (he0 : ∀ x, e01 (((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c
      (Scheme.TwoAffineOpenCover.specMap R A₀)) L).r0 x) =
    ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).ρ0
      (e0 x))
  (he1 : ∀ y, e01 (((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c
      (Scheme.TwoAffineOpenCover.specMap R A₀)) L).r1 y) =
    (t : ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
      A₀))).A01) *
      ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).ρ1
        (e1 y))

local notation "S₀" =>
  Scheme.TwoAffineOpenCover.sectionsOf (Scheme.TwoAffineOpenCover.pullback 𝒱 c A₀)
  (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) L
local notation "S'" =>
  Scheme.TwoAffineOpenCover.sectionsOf (Scheme.TwoAffineOpenCover.pullback 𝒱 c A')
  (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A')) (Functor.obj
    (Scheme.Modules.pullback
    (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))) L)

include hL he0 he1

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover in
theorem main :
    ∃ (e0' : (S').M0 ≃ₗ[(𝒰').A0] (𝒰').A0) (e1' : (S').M1 ≃ₗ[(𝒰').A1] (𝒰').A1)
      (e01' : (S').M01 ≃ₗ[(𝒰').A01] (𝒰').A01),
      (∀ x, e01' ((S').r0 x) = (𝒰').ρ0 (e0' x)) ∧
      (∀ y, e01' ((S').r1 y) =
        (show (𝒰').A01 from
          ((σst).appLE ((𝒱₀).U0 ⊓ (𝒱₀).U1) ((𝒱').U0 ⊓ (𝒱').U1) h01≤).hom (t : (𝒰₀).A01)) *
          (𝒰').ρ1 (e1' y)) := by
  obtain ⟨d0, d1, d01, hd0, hd1, -, -, -, hs0, hs1, hs01⟩ :=
    exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial
      𝒱 c A₀ A' L hL.1
  obtain ⟨k0, k1, k01, hk0, hk1, hk01⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_stage_baseChangeIsos_structureSheaf 𝒱 c A₀ A'
  set g0 : (S₀).M0 := e0.symm 1 with hg0
  set g1 : (S₀).M1 := e1.symm 1 with hg1
  set g01 : (S₀).M01 := e01.symm 1 with hg01
  have hr0 : (S₀).r0 g0 = g01 := by
    rw [hg01, eq_comm, LinearEquiv.symm_apply_eq, he0, hg0, LinearEquiv.apply_symm_apply, map_one]
  have hr1 : (S₀).r1 g1 = (t : (𝒰₀).A01) • g01 := by
    rw [hg01, ← linearEquiv_symm_apply_eq_smul, eq_comm, LinearEquiv.symm_apply_eq, he1, hg1,
      LinearEquiv.apply_symm_apply, map_one, mul_one]
  set η0 : (S').M0 := d0 ((1 : A') ⊗ₜ[A₀] g0) with hη0
  set η1 : (S').M1 := d1 ((1 : A') ⊗ₜ[A₀] g1) with hη1
  set η01 : (S').M01 := d01 ((1 : A') ⊗ₜ[A₀] g01) with hη01
  have hr0' : (S').r0 η0 = η01 := by
    rw [hη0, ← hd0, LinearMap.baseChange_tmul, hr0]
  have hr1' : (S').r1 η1 =
      (show (𝒰').A01 from
        ((σst).appLE ((𝒱₀).U0 ⊓ (𝒱₀).U1) ((𝒱').U0 ⊓ (𝒱').U1) h01≤).hom (t : (𝒰₀).A01)) • η01 := by
    rw [hη1, ← hd1, LinearMap.baseChange_tmul, hr1, hs01]
  have hbij0 : Function.Bijective (LinearMap.toSpanSingleton (𝒰').A0 (S').M0 η0) := by
    have key : (LinearMap.toSpanSingleton (𝒰').A0 (S').M0 η0) ∘ k0 =
        d0 ∘ (LinearEquiv.lTensor A' (e0.symm.restrictScalars A₀)) := by
      funext z
      induction z using TensorProduct.inductionOn with
      | add x y hx hy =>
        simp only [Function.comp_apply, map_add] at hx hy ⊢
        rw [hx, hy]
      | tmul a s =>
        simp only [Function.comp_apply, LinearMap.toSpanSingleton_apply, LinearEquiv.lTensor_tmul,
          LinearEquiv.restrictScalars_apply]
        rw [linearEquiv_symm_apply_eq_smul e0 s, ← hg0]
        have h1 : a ⊗ₜ[A₀] s = a • ((1 : A') ⊗ₜ[A₀] s) := by rw [smul_tmul', smul_eq_mul, mul_one]
        have h2 : a ⊗ₜ[A₀] (s • g0) = a • ((1 : A') ⊗ₜ[A₀] (s • g0)) :=
          by rw [smul_tmul', smul_eq_mul, mul_one]
        rw [h1, h2, map_smul, map_smul, hk0, hs0, ← hη0]
        exact smul_assoc a
          (show (𝒰').A0 from ((σst).appLE (𝒱₀).U0 (𝒱').U0 h0≤).hom s) η0
    have hc : Function.Bijective ((LinearMap.toSpanSingleton (𝒰').A0 (S').M0 η0) ∘ k0) := by
      rw [key]; exact d0.bijective.comp (LinearEquiv.lTensor A' (e0.symm.restrictScalars
        A₀)).bijective
    exact (Function.Bijective.of_comp_iff _ k0.bijective).mp hc
  have hbij1 : Function.Bijective (LinearMap.toSpanSingleton (𝒰').A1 (S').M1 η1) := by
    have key : (LinearMap.toSpanSingleton (𝒰').A1 (S').M1 η1) ∘ k1 =
        d1 ∘ (LinearEquiv.lTensor A' (e1.symm.restrictScalars A₀)) := by
      funext z
      induction z using TensorProduct.inductionOn with
      | add x y hx hy =>
        simp only [Function.comp_apply, map_add] at hx hy ⊢
        rw [hx, hy]
      | tmul a s =>
        simp only [Function.comp_apply, LinearMap.toSpanSingleton_apply, LinearEquiv.lTensor_tmul,
          LinearEquiv.restrictScalars_apply]
        rw [linearEquiv_symm_apply_eq_smul e1 s, ← hg1]
        have h1 : a ⊗ₜ[A₀] s = a • ((1 : A') ⊗ₜ[A₀] s) := by rw [smul_tmul', smul_eq_mul, mul_one]
        have h2 : a ⊗ₜ[A₀] (s • g1) = a • ((1 : A') ⊗ₜ[A₀] (s • g1)) :=
          by rw [smul_tmul', smul_eq_mul, mul_one]
        rw [h1, h2, map_smul, map_smul, hk1, hs1, ← hη1]
        exact smul_assoc a
          (show (𝒰').A1 from ((σst).appLE (𝒱₀).U1 (𝒱').U1 h1≤).hom s) η1
    have hc : Function.Bijective ((LinearMap.toSpanSingleton (𝒰').A1 (S').M1 η1) ∘ k1) := by
      rw [key]; exact d1.bijective.comp (LinearEquiv.lTensor A' (e1.symm.restrictScalars
        A₀)).bijective
    exact (Function.Bijective.of_comp_iff _ k1.bijective).mp hc
  have hbij01 : Function.Bijective (LinearMap.toSpanSingleton (𝒰').A01 (S').M01 η01) := by
    have key : (LinearMap.toSpanSingleton (𝒰').A01 (S').M01 η01) ∘ k01 =
        d01 ∘ (LinearEquiv.lTensor A' (e01.symm.restrictScalars A₀)) := by
      funext z
      induction z using TensorProduct.inductionOn with
      | add x y hx hy =>
        simp only [Function.comp_apply, map_add] at hx hy ⊢
        rw [hx, hy]
      | tmul a s =>
        simp only [Function.comp_apply, LinearMap.toSpanSingleton_apply, LinearEquiv.lTensor_tmul,
          LinearEquiv.restrictScalars_apply]
        rw [linearEquiv_symm_apply_eq_smul e01 s, ← hg01]
        have h1 : a ⊗ₜ[A₀] s = a • ((1 : A') ⊗ₜ[A₀] s) := by rw [smul_tmul', smul_eq_mul, mul_one]
        have h2 : a ⊗ₜ[A₀] (s • g01) = a • ((1 : A') ⊗ₜ[A₀] (s • g01)) :=
          by rw [smul_tmul', smul_eq_mul, mul_one]
        rw [h1, h2, map_smul, map_smul, hk01, hs01, ← hη01]
        exact smul_assoc a
          (show (𝒰').A01 from
            ((σst).appLE ((𝒱₀).U0 ⊓ (𝒱₀).U1) ((𝒱').U0 ⊓ (𝒱').U1) h01≤).hom s) η01
    have hc : Function.Bijective ((LinearMap.toSpanSingleton (𝒰').A01 (S').M01 η01) ∘ k01) := by
      rw [key]; exact d01.bijective.comp (LinearEquiv.lTensor A' (e01.symm.restrictScalars
        A₀)).bijective
    exact (Function.Bijective.of_comp_iff _ k01.bijective).mp hc
  let E0 := LinearEquiv.ofBijective _ hbij0
  let E1 := LinearEquiv.ofBijective _ hbij1
  let E01 := LinearEquiv.ofBijective _ hbij01
  refine ⟨E0.symm, E1.symm, E01.symm, fun x => ?_, fun y => ?_⟩
  · obtain ⟨b, rfl⟩ := E0.surjective x
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_eq]
    change (S').r0 (b • η0) = (𝒰').ρ0 b • η01
    rw [(S').r0_smul, hr0']
  · obtain ⟨b, rfl⟩ := E1.surjective y
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_eq]
    change (S').r1 (b • η1) = (_ * (𝒰').ρ1 b) • η01
    rw [(S').r1_smul, hr1', ← mul_smul, mul_comm]

end Main

end P2mTJ2stage

end
end Scheme_TwoAffineOpenCover_exists_sectionsOf_pullback_stageHom_equiv_lineBundle_appLE
end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open Scheme_TwoAffineOpenCover_exists_sectionsOf_pullback_stageHom_equiv_lineBundle_appLE in
theorem exists_sectionsOf_pullback_stageHom_equiv_lineBundle_appLE
    {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))
    (A₀ A' : Type u) [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A']
      [IsScalarTower R A₀ A']
    (L : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A₀)).Modules)
    (hL : Scheme.Modules.IsInvertible L)
    (t : ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
      A₀))).A01ˣ)
    (e0 : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
      A₀)) L).M0
      ≃ₗ[((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
        A₀))).A0]
      ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A0)
    (e1 : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
      A₀)) L).M1
      ≃ₗ[((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
        A₀))).A1]
      ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A1)
    (e01 : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap
      R A₀)) L).M01
      ≃ₗ[((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
        A₀))).A01]
      ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
        A₀))).A01)
    (he0 : ∀ x, e01 (((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c
        (Scheme.TwoAffineOpenCover.specMap R A₀)) L).r0 x) =
      ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).ρ0
        (e0 x))
    (he1 : ∀ y, e01 (((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c
        (Scheme.TwoAffineOpenCover.specMap R A₀)) L).r1 y) =
      (t : ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
        A₀))).A01) *
        ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
          A₀))).ρ1 (e1 y)) :
    ∃ (e0' : ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c
      (Scheme.TwoAffineOpenCover.specMap R A'))
          ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c
            (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj L)).M0
        ≃ₗ[((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
          A'))).A0]
        ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
          A'))).A0)
      (e1' : ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c
        (Scheme.TwoAffineOpenCover.specMap R A'))
          ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c
            (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj L)).M1
        ≃ₗ[((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
          A'))).A1]
        ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
          A'))).A1)
      (e01' : ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c
        (Scheme.TwoAffineOpenCover.specMap R A'))
          ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c
            (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj L)).M01
        ≃ₗ[((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
          A'))).A01]
        ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
          A'))).A01),
      (∀ x, e01' (((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c
        (Scheme.TwoAffineOpenCover.specMap R A'))
          ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c
            (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj L)).r0 x) =
        ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
          A'))).ρ0 (e0' x)) ∧
      (∀ y, e01' (((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c
        (Scheme.TwoAffineOpenCover.specMap R A'))
          ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c
            (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj L)).r1 y) =
        (show ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
          A'))).A01 from
          ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀
            A'))).appLE
            ((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1) ((𝒱.pullback c A').U0 ⊓ (𝒱.pullback c
              A').U1)
            (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom
          (t : ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
            A₀))).A01)) *
        ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R
          A'))).ρ1 (e1' y)) :=
  P2mTJ2stage.main 𝒱 c A₀ A' L hL t e0 e1 e01 he0 he1
end AlgebraicGeometry.Scheme.TwoAffineOpenCover
end ProofImplementation
