/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Flat_ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Nyll.SchemeTheory.Cohomology.Sheaves.CoherentBaseChange
import Nyll.AlgebraicCurves.Foundations.Algebra.Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range
import Nyll.AlgebraicCurves.Foundations.Algebra.Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range

/-!
# Module Flat ker base Change le range of forall ker base Change residue Field le range
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Module_Flat_ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range

universe u

open TensorProduct

theorem _root_.Module.Flat.ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i +
        1))).subtype))
    (hfib : ∀ i : ℕ,
      LinearMap.ker ((d (i + 1)).baseChange (IsLocalRing.ResidueField R)) ≤
        LinearMap.range ((d i).baseChange (IsLocalRing.ResidueField R))) :
    (∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i)) ∧
      ∀ (K : Type u) [Field K] [Algebra R K] (i : ℕ),
        LinearMap.ker ((d (i + 1)).baseChange K) ≤ LinearMap.range ((d i).baseChange K) := by
  have hex : ∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i) := by
    refine Module.Flat.ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range C d hdd n
      hbd hfin ?_
    intro 𝔪 h𝔪 i
    obtain rfl : 𝔪 = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal h𝔪
    exact hfib i
  exact ⟨hex, fun K _ _ i =>
    (Module.Flat.flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range C d hdd n hbd
    hex).2.2 K i⟩
end Module_Flat_ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range
end AlgebraicCurves.Foundations.Algebra.Proofs
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
attribute [-simp] TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq
