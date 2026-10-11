/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_Smooth_of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_perfectField

/-!
# Algebra Smooth of is Integrally Closed of krull Dim LE one of perfect Field
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace Algebra_Smooth_of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField

universe u v

open IsLocalRing

theorem _root_.Algebra.Smooth.of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField
    (k : Type u) [Field k] [PerfectField k] (B : Type v) [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] [IsIntegrallyClosed B] [Ring.KrullDimLE 1 B] :
    Algebra.Smooth k B := by
  classical
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hfp : Algebra.FinitePresentation k B := (Algebra.FinitePresentation.of_finiteType).mp
    inferInstance
  suffices hfs : Algebra.FormallySmooth k B from ⟨hfs, hfp⟩
  by_cases hB : IsField B
  · let : Field B := hB.toField
    have : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
    have : Algebra.IsSeparable k B := Algebra.IsAlgebraic.isSeparable_of_perfectField
    have : Algebra.FormallyEtale k B := Algebra.FormallyEtale.of_isSeparable k B
    infer_instance
  · have : Ring.DimensionLEOne B := ⟨fun hp hpp => hpp.isMaximal_of_ne_bot hp⟩
    have : IsDedekindDomain B := (isDedekindDomain_iff B (FractionRing B)).mpr
      ⟨inferInstance, inferInstance, inferInstance, fun hx => (isIntegrallyClosed_iff (FractionRing
        B)).mp inferInstance hx⟩
    have hmax : ∀ p : PrimeSpectrum B, p.asIdeal.IsMaximal → p ∈ Algebra.smoothLocus k B := by
      intro p hp
      change Algebra.FormallySmooth k (Localization.AtPrime p.asIdeal)
      have hne : p.asIdeal ≠ ⊥ := by
        intro h
        apply hB
        rw [Ring.isField_iff_maximal_bot, ← h]
        exact hp
      have : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
        IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hne _
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p.asIdeal)
      have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
      have hmaxI := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
      have : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
        IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance
      have : Algebra.EssFiniteType k (Localization.AtPrime p.asIdeal) :=
        Algebra.EssFiniteType.comp k B _
      exact Algebra.FormallySmooth.of_maximalIdeal_eq_span_of_perfectField k _ ϖ hϖ0 hmaxI
    rw [← Algebra.smoothLocus_eq_univ_iff]
    apply Set.eq_univ_of_forall
    intro p
    obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
    let M : PrimeSpectrum B := ⟨m, hm.isPrime⟩
    have hM : M ∈ Algebra.smoothLocus k B := hmax M hm
    by_contra hp
    have hclosed : IsClosed (Algebra.smoothLocus k B)ᶜ := Algebra.isOpen_smoothLocus.isClosed_compl
    have hcl : M ∈ closure ({p} : Set (PrimeSpectrum B)) := (PrimeSpectrum.le_iff_mem_closure p
      M).mp hpm
    have hsub : closure ({p} : Set (PrimeSpectrum B)) ⊆ (Algebra.smoothLocus k B)ᶜ :=
      hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hp)
    exact hsub hcl hM
end Algebra_Smooth_of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
