/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_isClosed_setOf_le_finrank_cohomology_baseChange_residueField_of_projective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import AlgebraicCurves.Cohomology.Cech.TwoChartCech_isClosed_setOf_le_finrank_ker_baseChange

/-!
# Module is Closed set Of le finrank cohomology base Change residue Field of projective
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.CohomologyFinrankClosed
attribute [-simp] CoherentBaseChange.FibreH0Family.mk.sizeOf_spec
  CoherentBaseChange.FibreH0Family.mk.injEq

universe u

open TensorProduct
open CategoryTheory AlgebraicGeometry

theorem _root_.Module.isClosed_setOf_le_finrank_cohomology_baseChange_residueField_of_projective
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Projective R (K i)]
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hδδ : ∀ i, δ (i + 1) ∘ₗ δ i = 0) (r : ℕ) :
    IsClosed {q : PrimeSpectrum R | r ≤ Module.finrank q.asIdeal.ResidueField
        ↥(LinearMap.ker ((δ 0).baseChange q.asIdeal.ResidueField))} ∧
      ∀ i : ℕ, IsClosed {q : PrimeSpectrum R |
        r + Module.finrank q.asIdeal.ResidueField
            ↥((LinearMap.range ((δ i).baseChange q.asIdeal.ResidueField)).comap
              (LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField)).subtype) ≤
          Module.finrank q.asIdeal.ResidueField
            ↥(LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField))} := by
  classical
  have hz : ∀ (j n : ℕ), IsClosed {q : PrimeSpectrum R | n ≤ Module.finrank q.asIdeal.ResidueField
    ↥(LinearMap.ker ((δ j).baseChange q.asIdeal.ResidueField))} := by
    intro j n
    exact TwoChartCech.isClosed_setOf_le_finrank_ker_baseChange (δ j) (𝟙 (Spec (.of R))) n
  refine ⟨hz 0 r, fun i => ?_⟩
  have hpt : ∀ q : PrimeSpectrum R, Module.finrank q.asIdeal.ResidueField ↥((LinearMap.range ((δ
    i).baseChange q.asIdeal.ResidueField)).comap (LinearMap.ker ((δ (i + 1)).baseChange
    q.asIdeal.ResidueField)).subtype) + Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ
    i).baseChange q.asIdeal.ResidueField)) = Module.rankAtStalk (K i) q := by
    intro q
    have hle : LinearMap.range ((δ i).baseChange q.asIdeal.ResidueField) ≤ LinearMap.ker ((δ (i +
      1)).baseChange q.asIdeal.ResidueField) := by
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hδδ i]
      simp
    rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq, Module.rankAtStalk_eq]
    exact LinearMap.finrank_range_add_finrank_ker _
  have hset : {q : PrimeSpectrum R | r + Module.finrank q.asIdeal.ResidueField ↥((LinearMap.range
    ((δ i).baseChange q.asIdeal.ResidueField)).comap (LinearMap.ker ((δ (i + 1)).baseChange
    q.asIdeal.ResidueField)).subtype) ≤ Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ
    (i + 1)).baseChange q.asIdeal.ResidueField))} =
      {q : PrimeSpectrum R | r + Module.rankAtStalk (K i) q ≤ Module.finrank
        q.asIdeal.ResidueField ↥(LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField)) +
        Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ i).baseChange
        q.asIdeal.ResidueField))} := by
    ext q
    simp only [Set.mem_ofPred_eq]
    have h := hpt q
    constructor
    · intro h'; omega
    · intro h'; omega
  rw [hset]
  have hsum : ∀ m : ℕ, IsClosed {q : PrimeSpectrum R | m ≤ Module.finrank q.asIdeal.ResidueField
    ↥(LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField)) + Module.finrank
    q.asIdeal.ResidueField ↥(LinearMap.ker ((δ i).baseChange q.asIdeal.ResidueField))} := by
    intro m
    have heq : {q : PrimeSpectrum R | m ≤ Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker
      ((δ (i + 1)).baseChange q.asIdeal.ResidueField)) + Module.finrank q.asIdeal.ResidueField
      ↥(LinearMap.ker ((δ i).baseChange q.asIdeal.ResidueField))} =
        ⋃ a ∈ Finset.range (m + 1),
          ({q : PrimeSpectrum R | a ≤ Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ (i
            + 1)).baseChange q.asIdeal.ResidueField))} ∩ {q : PrimeSpectrum R | m - a ≤
            Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ i).baseChange
            q.asIdeal.ResidueField))}) := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Finset.mem_range,
        exists_prop]
      constructor
      · intro h
        exact ⟨min m (Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ (i + 1)).baseChange
          q.asIdeal.ResidueField))), by omega, by omega, by omega⟩
      · rintro ⟨a, ha, h1, h2⟩
        omega
    rw [heq]
    exact isClosed_biUnion_finset fun a _ => (hz (i + 1) a).inter (hz i (m - a))
  have : Module.FinitePresentation R (K i) := Module.finitePresentation_of_projective R (K i)
  have hρ : IsLocallyConstant (Module.rankAtStalk (R := R) (K i)) :=
    Module.isLocallyConstant_rankAtStalk
  rw [← isOpen_compl_iff]
  have hcompl : {q : PrimeSpectrum R | r + Module.rankAtStalk (K i) q ≤ Module.finrank
    q.asIdeal.ResidueField ↥(LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField)) +
    Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ i).baseChange
    q.asIdeal.ResidueField))}ᶜ =
      ⋃ c : ℕ, ({q : PrimeSpectrum R | Module.rankAtStalk (K i) q = c} ∩
        {q : PrimeSpectrum R | r + c ≤ Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ
          (i + 1)).baseChange q.asIdeal.ResidueField)) + Module.finrank q.asIdeal.ResidueField
          ↥(LinearMap.ker ((δ i).baseChange q.asIdeal.ResidueField))}ᶜ) := by
    ext q
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨_, rfl, h⟩
    · rintro ⟨c, rfl, h⟩
      exact h
  rw [hcompl]
  exact isOpen_iUnion fun c => (hρ.isOpen_fiber c).inter (hsum (r + c)).isOpen_compl
end AlgebraicCurves.Foundations.Algebra.Proofs.CohomologyFinrankClosed
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
  CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq
