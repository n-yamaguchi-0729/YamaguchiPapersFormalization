/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_cechRiemannRoch_of_genusReached.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.FiniteDimensional_lSpace
import Nyll.AlgebraicCurves.Cohomology.IndexOfSpecialty_eq_finrank_H1
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.IndexOfSpecialty_eq_of_genusReached
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.RiemannGenusReachedAt_eq_of_ge
import Nyll.AlgebraicCurves.Cohomology.Finite_H1_of_genusReached
import Nyll.AlgebraicCurves.Cohomology.CechH1ToH1_bijective

/-!
The Riemann--Roch dimension formula from a two-chart section system reaching the genus.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Proofs.CechRiemannRoch_of_genusReached

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.cechRiemannRoch_of_genusReached {K F : Type*} [Field K] [Field F]
    [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁)
    (D : Divisor K F) :
    FiniteDimensional K ↥(cechH0 S₀ S₁ D) ∧ Module.Finite K (cechH1 S₀ S₁ D) ∧
      Module.finrank K ↥(cechH0 S₀ S₁ D) = ell D ∧
      Module.finrank K (cechH1 S₀ S₁ D) = indexOfSpecialty D ∧
      (Module.finrank K ↥(cechH0 S₀ S₁ D) : ℤ) - Module.finrank K (cechH1 S₀ S₁ D)
        = Divisor.degree D + 1 - γ ∧
      (D₀ ≤ D → Subsingleton (cechH1 S₀ S₁ D)) := by
  obtain ⟨v₀, hv₀⟩ := h₀
  have : Nonempty (Place K F) := ⟨v₀⟩
  have : FiniteDimensional K ↥(LSpace D) := finiteDimensional_lSpace (K := K) (F := F) D
  have : Module.Finite K (H1 D) := finite_H1_of_genusReached h D
  let e0 := cechH0Equiv hcover D
  let e1 : cechH1 S₀ S₁ D ≃ₗ[K] H1 D :=
    LinearEquiv.ofBijective (cechH1ToH1 hcover D) (cechH1ToH1_bijective h hcover ⟨v₀, hv₀⟩ h₁ D)
  have : Module.Finite K (cechH1 S₀ S₁ D) := Module.Finite.equiv e1.symm
  have h0 : Module.finrank K ↥(cechH0 S₀ S₁ D) = ell D := e0.finrank_eq
  have h1 : Module.finrank K (cechH1 S₀ S₁ D) = indexOfSpecialty D := by
    rw [e1.finrank_eq, indexOfSpecialty_eq_finrank_H1]
  obtain ⟨-, hidx⟩ := indexOfSpecialty_eq_of_genusReached h D
  refine ⟨LinearEquiv.finiteDimensional e0.symm, inferInstance, h0, h1, ?_, fun hD => ?_⟩
  · rw [h0, h1]; omega
  · have hreach := h.eq_of_ge hD
    have hi0 : Module.finrank K (cechH1 S₀ S₁ D) = 0 := by
      have : (indexOfSpecialty D : ℤ) = 0 := by rw [hidx]; omega
      rw [h1]; exact_mod_cast this
    exact Module.finrank_zero_iff.mp hi0
end AlgebraicCurves.Cohomology.Proofs.CechRiemannRoch_of_genusReached
end ProofImplementation
