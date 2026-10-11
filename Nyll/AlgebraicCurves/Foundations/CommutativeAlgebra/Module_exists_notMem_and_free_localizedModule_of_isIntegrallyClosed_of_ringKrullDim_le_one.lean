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

import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.Submodule

/-!
# Module exists not Mem and free localized Module of is Integrally Closed of ring Krull Dim
le one
-/

section ProofImplementation

namespace Module

universe u

theorem
  _root_.Module.exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (𝔭 : Ideal A) [𝔭.IsPrime]
    (h𝔭ic : IsIntegrallyClosed (Localization.AtPrime 𝔭)) (h𝔭dim : ringKrullDim
      (Localization.AtPrime 𝔭) ≤ 1)
    (B : Type u) [AddCommGroup B] [Module A B] [Module.Finite A B] [NoZeroSMulDivisors A B] :
    ∃ f : A, f ∉ 𝔭 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) B) :=
      by
  classical
  set Aₚ := Localization.AtPrime 𝔭 with hAₚ
  have : IsNoetherianRing Aₚ := IsLocalization.isNoetherianRing 𝔭.primeCompl Aₚ inferInstance
  have : IsDomain Aₚ := IsLocalization.isDomain_localization 𝔭.primeCompl_le_nonZeroDivisors
  have : Ring.KrullDimLE 1 Aₚ := Ring.krullDimLE_iff.mpr h𝔭dim
  have : Ring.DimensionLEOne Aₚ := ⟨fun hne hp => Ideal.IsPrime.isMaximal_of_ne_bot hp hne⟩
  have : IsDedekindRing Aₚ := { (inferInstance : IsNoetherian Aₚ Aₚ), (inferInstance :
    Ring.DimensionLEOne Aₚ), h𝔭ic with }
  have : IsDedekindDomain Aₚ := {}
  have : IsPrincipalIdealRing Aₚ := inferInstance
  have : Module.IsTorsionFree A B := inferInstance
  have : Module.Finite Aₚ (LocalizedModule 𝔭.primeCompl B) := inferInstance
  have : Module.IsTorsionFree Aₚ (LocalizedModule 𝔭.primeCompl B) := inferInstance
  have : Module.Free Aₚ (LocalizedModule 𝔭.primeCompl B) := Module.free_of_finite_type_torsion_free'
  have : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    𝔭.primeCompl
    (LocalizedModule.mkLinearMap 𝔭.primeCompl B) (Localization.AtPrime 𝔭)
  exact ⟨r, hr, hfree⟩
end Module
end ProofImplementation
