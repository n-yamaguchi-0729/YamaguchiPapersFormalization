/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Flat_exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import SchemeTheory.Cohomology.Cech.TwoChartCech
import AlgebraicCurves.Foundations.Algebra.Module_Flat_exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range
import AlgebraicCurves.Foundations.CommutativeAlgebra.Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range
import AlgebraicCurves.Foundations.Algebra.Module_exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor

/-!
# Module Flat exists forall is Unit projective ker base Change of ker base Change residue
Field le range
-/

section ProofImplementation

namespace Module.Flat

universe u

open _root_.TensorProduct

theorem exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i +
        1))).subtype))
    (𝔭 : PrimeSpectrum R)
    (hfib : ∀ i : ℕ,
      LinearMap.ker ((d (i + 1)).baseChange 𝔭.asIdeal.ResidueField) ≤
        LinearMap.range ((d i).baseChange 𝔭.asIdeal.ResidueField)) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g) →
        Module.Finite A (LinearMap.ker ((d 0).baseChange A)) ∧
        Module.Projective A (LinearMap.ker ((d 0).baseChange A)) ∧
        (∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A)) ∧
        Function.Bijective (TwoChartCech.kerBaseChangeHom (d 0) A) ∧
        (∀ 𝔮 : PrimeSpectrum A,
          Module.rankAtStalk (LinearMap.ker ((d 0).baseChange A)) 𝔮 =
            Module.finrank 𝔭.asIdeal.ResidueField (LinearMap.ker ((d 0).baseChange
              𝔭.asIdeal.ResidueField))) := by
  classical
  obtain ⟨g, hg, hexS⟩ :=
    Module.Flat.exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range
      C d hdd n hbd hfin 𝔭 hfib
  have hB2 := fun (A : Type u) [CommRing A] [Algebra R A] (hA : IsUnit (algebraMap R A g)) =>
    Module.Flat.projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range
      C d hdd n hbd hfin0 g (Localization.Away g) (hexS (Localization.Away g)) A hA
  have := hfin0
  have hproj : ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g) →
      Module.Projective A (A ⊗[R] LinearMap.ker (d 0)) := by
    intro A _ _ hA
    obtain ⟨-, hP, -, hbij⟩ := hB2 A hA
    exact Module.Projective.of_equiv (LinearEquiv.ofBijective (TwoChartCech.kerBaseChangeHom (d 0)
      A) hbij).symm
  obtain ⟨g', hg', hunit, hrank⟩ :=
    Module.exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor
      (LinearMap.ker (d 0)) 𝔭 g hg hproj
  refine ⟨g', hg', fun A _ _ hA => ?_⟩
  obtain ⟨hf, hP, hex, hbij⟩ := hB2 A (hunit A hA)
  refine ⟨hf, hP, hex, hbij, fun 𝔮 => ?_⟩
  have hκ : IsUnit (algebraMap R 𝔭.asIdeal.ResidueField g) := by
    rw [isUnit_iff_ne_zero, ne_eq, Ideal.algebraMap_residueField_eq_zero]
    exact hg
  obtain ⟨-, -, -, hbijκ⟩ := hB2 𝔭.asIdeal.ResidueField hκ
  rw [← Module.rankAtStalk_eq_of_equiv (LinearEquiv.ofBijective (TwoChartCech.kerBaseChangeHom (d
    0) A) hbij),
    hrank A hA 𝔮,
    ← (LinearEquiv.ofBijective (TwoChartCech.kerBaseChangeHom (d 0) 𝔭.asIdeal.ResidueField)
      hbijκ).finrank_eq]
end Module.Flat
end ProofImplementation
