/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Flat_projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Flat.EquationalCriterion
import SchemeTheory.Cohomology.Cech.TwoChartCech
import AlgebraicCurves.Foundations.Algebra.Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range
import AlgebraicCurves.Foundations.Algebra.Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range

/-!
# Module Flat projective ker and bijective ker Base Change Hom of forall ker base Change le
range
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.ProjectiveKernelBaseChange

universe u

open TensorProduct

theorem
  _root_.Module.Flat.projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i +
        1))).subtype))
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K] (i : ℕ),
      LinearMap.ker ((d (i + 1)).baseChange K) ≤ LinearMap.range ((d i).baseChange K)) :
    Module.Projective R (LinearMap.ker (d 0)) ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerBaseChangeHom (d 0) A)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A] (i : ℕ),
        LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A) := by
  have hex : ∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i) :=
    Module.Flat.ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range C d hdd n hbd hfin
      (fun 𝔪 _ i => by let := Ideal.Quotient.field 𝔪; exact hfib (R ⧸ 𝔪) i)
  obtain ⟨hflat, hbij, hc⟩ :=
    Module.Flat.flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range C d hdd n hbd hex
  refine ⟨?_, hbij, hc⟩
  have := hflat
  have := hfin0
  have : Module.FinitePresentation R ↥(LinearMap.ker (d 0)) := Module.finitePresentation_of_finite
    R _
  exact Module.Flat.projective_of_finitePresentation
end AlgebraicCurves.Foundations.Algebra.Proofs.ProjectiveKernelBaseChange
end ProofImplementation
