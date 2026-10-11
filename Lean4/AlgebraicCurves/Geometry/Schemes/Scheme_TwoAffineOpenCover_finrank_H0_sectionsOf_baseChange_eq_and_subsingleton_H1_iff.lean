/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_sectionsOf_baseChange_equiv_of_locallyTrivial
import AlgebraicCurves.Cohomology.Cech.TwoChartCech_finrank_ker_baseChange_eq_of_field_extension

/-!
# Ranks and vanishing of two-chart cohomology after a field extension

The base-change equivalences of sections on two affine charts and their overlap
identify zeroth-cohomology rank and the vanishing of first cohomology across a field extension.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_TwoAffineOpenCover_finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace CechFieldBCSketch

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

theorem main
    {P0 P1 P01 : Type u} [AddCommGroup P0] [Module k P0] [AddCommGroup P1] [Module k P1]
        [AddCommGroup P01] [Module k P01]
    (r0 : P0 →ₗ[k] P01) (r1 : P1 →ₗ[k] P01)
    {Q0 Q1 Q01 : Type u} [AddCommGroup Q0] [Module k' Q0] [AddCommGroup Q1] [Module k' Q1]
        [AddCommGroup Q01] [Module k' Q01]
    (s0 : Q0 →ₗ[k'] Q01) (s1 : Q1 →ₗ[k'] Q01)
    (e0 : k' ⊗[k] P0 ≃ₗ[k'] Q0) (e1 : k' ⊗[k] P1 ≃ₗ[k'] Q1) (e01 : k' ⊗[k] P01 ≃ₗ[k'] Q01)
    (h0 : ∀ x, e01 ((r0.baseChange k') x) = s0 (e0 x)) (h1 : ∀ x, e01 ((r1.baseChange k') x) =
        s1 (e1 x)) :
    Module.finrank k' (LinearMap.ker ((-s0).coprod s1)) = Module.finrank k (LinearMap.ker
        ((-r0).coprod r1)) ∧
      (Subsingleton (Q01 ⧸ LinearMap.range ((-s0).coprod s1)) ↔ Subsingleton (P01 ⧸
          LinearMap.range ((-r0).coprod r1))) := by
  classical
  set d : P0 × P1 →ₗ[k] P01 := (-r0).coprod r1 with hd
  set d' : Q0 × Q1 →ₗ[k'] Q01 := (-s0).coprod s1 with hd'
  let E : k' ⊗[k] (P0 × P1) ≃ₗ[k'] Q0 × Q1 := TensorProduct.prodRight k k' k' P0 P1 ≪≫ₗ
      e0.prodCongr e1
  have hsq : ∀ z, e01 ((d.baseChange k') z) = d' (E z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a p =>
      obtain ⟨p0, p1⟩ := p
      have ha0 : (a ⊗ₜ[k] p0 : k' ⊗[k] P0) = a • ((1 : k') ⊗ₜ[k] p0) := by rw
          [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have ha1 : (a ⊗ₜ[k] p1 : k' ⊗[k] P1) = a • ((1 : k') ⊗ₜ[k] p1) := by rw
          [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have ha01 : ∀ q : P01, (a ⊗ₜ[k] q : k' ⊗[k] P01) = a • ((1 : k') ⊗ₜ[k] q) := fun q => by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hr0 : e01 (a ⊗ₜ[k] r0 p0) = s0 (e0 (a ⊗ₜ[k] p0)) := by
        have := h0 (a ⊗ₜ[k] p0); rwa [LinearMap.baseChange_tmul] at this
      have hr1 : e01 (a ⊗ₜ[k] r1 p1) = s1 (e1 (a ⊗ₜ[k] p1)) := by
        have := h1 (a ⊗ₜ[k] p1); rwa [LinearMap.baseChange_tmul] at this
      simp only [E, d, d', LinearMap.baseChange_tmul, LinearMap.coprod_apply,
          LinearMap.neg_apply, LinearEquiv.trans_apply,
        TensorProduct.prodRight_tmul, LinearEquiv.prodCongr_apply, TensorProduct.tmul_add,
            TensorProduct.tmul_neg, map_add,
        map_neg, hr0, hr1]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcomp : (e01 : k' ⊗[k] P01 →ₗ[k'] Q01) ∘ₗ d.baseChange k' = d' ∘ₗ (E : k' ⊗[k] (P0 × P1)
      →ₗ[k'] Q0 × Q1) :=
    LinearMap.ext hsq
  have hd'eq : d' = ((e01 : k' ⊗[k] P01 →ₗ[k'] Q01) ∘ₗ d.baseChange k') ∘ₗ (E.symm : Q0 × Q1
      →ₗ[k'] k' ⊗[k] (P0 × P1)) := by
    rw [hcomp, LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.comp_id]
  have hker : LinearMap.ker d' = (LinearMap.ker (d.baseChange k')).map (E : k' ⊗[k] (P0 × P1)
      →ₗ[k'] Q0 × Q1) := by
    rw [hd'eq, LinearMap.ker_comp, LinearMap.ker_comp_of_ker_eq_bot _ e01.ker,
        Submodule.map_equiv_eq_comap_symm]
  have hfin1 : Module.finrank k' (LinearMap.ker d') = Module.finrank k' (LinearMap.ker
      (d.baseChange k')) := by
    rw [hker, LinearEquiv.finrank_map_eq]
  have hfin2 : Module.finrank k (LinearMap.ker (d.baseChange k)) = Module.finrank k'
      (LinearMap.ker (d.baseChange k')) :=
    TwoChartCech.finrank_ker_baseChange_eq_of_field_extension d k k'
  have hlid : LinearMap.ker (d.baseChange k) =
      (LinearMap.ker d).map ((TensorProduct.lid k (P0 × P1)).symm : P0 × P1 →ₗ[k] k ⊗[k] (P0 ×
          P1)) := by
    have hcomp' : d.baseChange k = ((TensorProduct.lid k P01).symm : P01 →ₗ[k] k ⊗[k] P01) ∘ₗ d ∘ₗ
        (TensorProduct.lid k (P0 × P1) : k ⊗[k] (P0 × P1) →ₗ[k] P0 × P1) := by
      apply TensorProduct.ext'
      intro a p
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
          TensorProduct.lid_tmul]
      rw [map_smul, map_smul, TensorProduct.lid_symm_apply, TensorProduct.smul_tmul',
          smul_eq_mul, mul_one]
    rw [hcomp', LinearMap.ker_comp_of_ker_eq_bot _ (TensorProduct.lid k P01).symm.ker,
        LinearMap.ker_comp,
      Submodule.comap_equiv_eq_map_symm]
  have hfin3 : Module.finrank k (LinearMap.ker (d.baseChange k)) = Module.finrank k
      (LinearMap.ker d) := by
    rw [hlid, LinearEquiv.finrank_map_eq]
  refine ⟨by rw [hfin1, ← hfin2, hfin3], ?_⟩
  have hrange : LinearMap.range d' = (LinearMap.range (d.baseChange k')).map (e01 : k' ⊗[k] P01
      →ₗ[k'] Q01) := by
    rw [hd'eq, LinearMap.range_comp_of_range_eq_top _ E.symm.range, LinearMap.range_comp]
  have step1 : Subsingleton (Q01 ⧸ LinearMap.range d') ↔ LinearMap.range (d.baseChange k') = ⊤ := by
    rw [Submodule.Quotient.subsingleton_iff, hrange, Submodule.map_eq_top_iff]
  have step2 : LinearMap.range (d.baseChange k') = ⊤ ↔
      Subsingleton ((k' ⊗[k] P01) ⧸ LinearMap.range (d.lTensor k')) := by
    rw [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top, LinearMap.range_eq_top,
      LinearMap.baseChange_eq_ltensor]
  have hex : Function.Exact (d.lTensor k') ((LinearMap.range d).mkQ.lTensor k') :=
    lTensor_exact k' (LinearMap.exact_map_mkQ_range d) (Submodule.mkQ_surjective _)
  have hsurj : Function.Surjective ((LinearMap.range d).mkQ.lTensor k') :=
    LinearMap.lTensor_surjective k' (Submodule.mkQ_surjective _)
  have step3 : Subsingleton ((k' ⊗[k] P01) ⧸ LinearMap.range (d.lTensor k')) ↔
      Subsingleton (k' ⊗[k] (P01 ⧸ LinearMap.range d)) :=
    Equiv.subsingleton_congr (hex.linearEquivOfSurjective hsurj).toEquiv
  have step4 : Subsingleton (k' ⊗[k] (P01 ⧸ LinearMap.range d)) ↔ Subsingleton (P01 ⧸
      LinearMap.range d) :=
    Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right k k'
  exact step1.trans (step2.trans (step3.trans step4))

end CechFieldBCSketch

open CechFieldBCSketch in
with_weak_namespace _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
theorem finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (𝒱 :
        X.TwoAffineOpenCover)
    (M : X.Modules)
    (hM : ∀ p : X, ∃ U : X.Opens, p ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (k' : Type u) [Field k'] [Algebra k k'] :
    Module.finrank k'
        ((𝒱.pullback x k').sectionsOf (pullback.snd x (Scheme.TwoAffineOpenCover.specMap k k'))
          ((Scheme.Modules.pullback (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k
              k'))).obj M)).H0 =
      Module.finrank k (𝒱.sectionsOf x M).H0 ∧
    (Subsingleton ((𝒱.pullback x k').sectionsOf (pullback.snd x
        (Scheme.TwoAffineOpenCover.specMap k k'))
          ((Scheme.Modules.pullback (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k
              k'))).obj M)).H1 ↔
      Subsingleton (𝒱.sectionsOf x M).H1) := by
  obtain ⟨e0, e1, e01, h0, h1, -, -, -⟩ :=
    Scheme.TwoAffineOpenCover.exists_sectionsOf_baseChange_equiv_of_locallyTrivial 𝒱 x M hM k'
  exact (open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
    open Scheme_TwoAffineOpenCover_finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff in
    CechFieldBCSketch.main _ _ _ _ e0 e1 e01 h0 h1)
end Scheme_TwoAffineOpenCover_finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
