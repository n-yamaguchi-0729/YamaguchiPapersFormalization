/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_neg_le_ord_trace_of_forall_le_ord_of_isCurveOver.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Cohomology.Cech.Maps
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.FunctionFields.TraceIntegralAlong_of_separableAlong
import Nyll.AlgebraicCurves.Places.Place_mem_iff_ord_nonneg

/-!
# Place neg le ord trace of forall le ord of is Curve Over
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_neg_le_ord_trace_of_forall_le_ord_of_isCurveOver

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace TraceFloor
open _root_.AlgebraicCurve

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']

theorem exists_ord_eq_one (x : Place k F) : ∃ π : F, x.ord π = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible x.toValuationSubring
  exact ⟨(π : F), x.ord_coe_irreducible hπ⟩

theorem ord_nonneg_of_mem' (v : Place k F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f :=
  by
  by_cases h0 : f = 0
  · rw [h0, Place.ord_zero]
  · exact (Place.mem_iff_ord_nonneg v h0).mp hf

theorem ord_pow' (v : Place k F) (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  have := v.ord_zpow f (n : ℤ)
  rwa [zpow_natCast] at this

theorem main (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong k φ)
    (hsep : SeparableAlong k φ)
    (x : Place k F) (S : Finset (Place k F')) (hS : ∀ y : Place k F', y ∈ S ↔ y.restrictAlong φ hφ
      = x)
    (a : ℤ) (ha : 0 ≤ a) (g : F')
    (hg : ∀ y ∈ S, -((Place.ramificationIndexAlong φ y : ℤ) * a) ≤ y.ord g) :
    letI := AlgebraicCurve.algebraAlong φ;
    -a ≤ x.ord (Algebra.trace F F' g) := by
  let := AlgebraicCurve.algebraAlong φ
  have := isScalarTower_along φ
  change -a ≤ x.ord (Algebra.trace F F' g)
  by_cases hT0 : Algebra.trace F F' g = 0
  · rw [hT0, Place.ord_zero]; linarith
  have hg0 : g ≠ 0 := by
    intro h; apply hT0; rw [h, map_zero]
  obtain ⟨π, hπ⟩ := exists_ord_eq_one x
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hπ; exact zero_ne_one hπ
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  set u : F' := φ (π ^ n) * g with hu
  have hφπ : φ (π ^ n) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero _ ((map_ne_zero φ).mpr hπ0)
  have hu0 : u ≠ 0 := mul_ne_zero hφπ hg0
  have hint : ∀ y : Place k F', y.restrictAlong φ hφ = x → u ∈ y.toValuationSubring := by
    intro y hy
    have hyS : y ∈ S := (hS y).mpr hy
    apply (Place.mem_iff_ord_nonneg y hu0).mpr
    rw [hu, y.ord_mul hφπ hg0, Place.ord_restrictAlong φ hφ y (π ^ n), hy, ord_pow', hπ, mul_one]
    have := hg y hyS
    linarith
  have htr : traceFunAlong φ u ∈ x.toValuationSubring :=
    AlgebraicCurve.traceIntegralAlong_of_separableAlong φ hφ hfin hsep x u hint
  rw [traceFunAlong_apply] at htr
  have hTu : Algebra.trace F F' u = π ^ n * Algebra.trace F F' g := by
    have e1 : u = (π ^ n) • g := by rw [hu, Algebra.smul_def]; rfl
    rw [e1, map_smul, smul_eq_mul]
  rw [hTu] at htr
  have h0 := ord_nonneg_of_mem' x htr
  rw [x.ord_mul (pow_ne_zero _ hπ0) hT0, ord_pow', hπ, mul_one] at h0
  linarith

end AlgebraicCurve.TraceFloor

theorem _root_.AlgebraicCurve.Place.neg_le_ord_trace_of_forall_le_ord_of_isCurveOver
    {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F'] [IsAlgClosed k]
    [IsCurveOver k F] [IsCurveOver k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong k φ) (hsep : SeparableAlong
      k φ)
    (x : Place k F) (S : Finset (Place k F')) (hS : ∀ y : Place k F', y ∈ S ↔ y.restrictAlong φ hφ
      = x)
    (a : ℤ) (ha : 0 ≤ a) (g : F') (hg : ∀ y ∈ S, -((Place.ramificationIndexAlong φ y : ℤ) * a) ≤
      y.ord g) :
    letI := AlgebraicCurve.algebraAlong φ;
    -a ≤ x.ord (Algebra.trace F F' g) :=
  AlgebraicCurve.TraceFloor.main φ hφ hfin hsep x S hS a ha g hg
end AlgebraicCurves.Places.Proofs.Place_neg_le_ord_trace_of_forall_le_ord_of_isCurveOver
end ProofImplementation

attribute [-instance] TwoChartCech.Sections.M0_moduleA
attribute [-instance] TwoChartCech.Sections.M1_module
attribute [-instance] TwoChartCech.Cover.A01_algebra
attribute [-instance] TwoChartCech.Cover.A0_algebra
attribute [-instance] TwoChartCech.Cover.A1_commRing
attribute [-instance] TwoChartCech.Cover.A1_algebra
attribute [-instance] TwoChartCech.Sections.M01_module
attribute [-instance] TwoChartCech.Sections.M0_addCommGroup
attribute [-instance] TwoChartCech.Sections.M0_tower
attribute [-instance] TwoChartCech.Sections.M01_addCommGroup
attribute [-instance] TwoChartCech.Cover.A0_commRing
attribute [-instance] TwoChartCech.Sections.M1_tower
attribute [-instance] TwoChartCech.Sections.M01_moduleA
attribute [-instance] TwoChartCech.Sections.M0_module
attribute [-instance] TwoChartCech.Sections.M1_moduleA
attribute [-instance] TwoChartCech.Sections.M1_addCommGroup
attribute [-instance] TwoChartCech.Cover.A01_commRing
attribute [-instance] TwoChartCech.Sections.M01_tower
attribute [-instance] CoherentBaseChange.TwoTermComplex.C0_module
attribute [-instance] CoherentBaseChange.TwoTermComplex.C0_addCommGroup
attribute [-instance] CoherentBaseChange.TwoTermComplex.C1_module
attribute [-instance] CoherentBaseChange.TwoTermComplex.C1_addCommGroup
attribute [-instance] CoherentBaseChange.TwoTermComplex.C0_free
attribute [-instance] CoherentBaseChange.TwoTermComplex.C1_finite
attribute [-instance] CoherentBaseChange.TwoTermComplex.C0_finite
attribute [-instance] CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicCurve.cechH1.traceAlong_mk
attribute [-simp] AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply
attribute [-simp] AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply
attribute [-simp] AlgebraicCurve.cechH1.pullbackAlong_mk
attribute [-simp] AlgebraicCurve.coe_cechH0Equiv_apply
attribute [-simp] AlgebraicCurve.cechH1ToH1_mk
attribute [-simp] AlgebraicCurve.lSpaceOn_univ
attribute [-simp] AlgebraicCurve.lSpaceOn_empty
attribute [-simp] TwoChartCech.Sections.mk.injEq
attribute [-simp] TwoChartCech.Cover.mk.injEq
attribute [-simp] TwoChartCech.GrothendieckComplex.mk.injEq
attribute [-simp] TwoChartCech.Sections.mk.sizeOf_spec
attribute [-simp] TwoChartCech.Cover.mk.sizeOf_spec
attribute [-simp] TwoChartCech.Cover.lineBundle_r0_apply
attribute [-simp] TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
attribute [-simp] TwoChartCech.Cover.lineBundle_r1_apply
attribute [-simp] CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
attribute [-simp] CoherentBaseChange.TwoTermComplex.mk.injEq
