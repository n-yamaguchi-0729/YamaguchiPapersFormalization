/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic
import AlgebraicCurves.Geometry.Schemes.MumfordTruncation
import AlgebraicCurves.Cohomology.Cech.TwoChartCech_Mumford_bijective_kerMapBaseChange
import AlgebraicCurves.Cohomology.Cech.TwoChartCech_Mumford_finite_K0

/-!
# finite ker base Change of finite ker of finite coker
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.finite_ker_baseChange_of_finite_ker_of_finite_coker

universe u

open scoped TensorProduct

theorem _root_.TwoChartCech.finite_ker_baseChange_of_finite_ker_of_finite_coker
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (A : Type u) [CommRing A] [Algebra R A] [IsNoetherianRing A] :
    Module.Finite A (LinearMap.ker (d.baseChange A)) := by
  have hbij := TwoChartCech.Mumford.bijective_kerMapBaseChange d A
  have : Module.Finite R ↥(TwoChartCech.Mumford.K0 d) := TwoChartCech.Mumford.finite_K0 d
  have : Module.Finite A (A ⊗[R] ↥(TwoChartCech.Mumford.K0 d)) := inferInstance
  have : IsNoetherian A (A ⊗[R] ↥(TwoChartCech.Mumford.K0 d)) :=
    isNoetherian_of_isNoetherianRing_of_finite A _
  have : Module.Finite A ↥(LinearMap.ker ((TwoChartCech.Mumford.dK d).baseChange A)) :=
    inferInstance
  exact Module.Finite.of_surjective _ hbij.2
end AlgebraicCurves.Cohomology.Cech.Proofs.finite_ker_baseChange_of_finite_ker_of_finite_coker
end ProofImplementation

attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq
