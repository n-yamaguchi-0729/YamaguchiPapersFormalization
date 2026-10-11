/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.PuncturedSpectrumHypersurfaceComponents

/-!
# Ideal-theoretic reduction for punctured hypersurface connectedness

A finite partition of the irreducible components of a principal hypersurface
gives two finite families of minimal primes.  If every component from one
family meets every component from the other only at the closed point, the
radical of the sum of the two component intersections is the maximal ideal.
This is the exact ideal-theoretic configuration to which the missing
complete-local intersection inequality applies.
-/

noncomputable section

open IsLocalRing

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- A prime containing the intersection of a finite family of ideals
contains one member of that family. -/
theorem exists_mem_le_of_sInf_le_prime_of_finite
    {C : Type u} [CommRing C]
    {S : Set (Ideal C)} (hS : S.Finite)
    {P : Ideal C} [P.IsPrime] (h : sInf S ≤ P) :
    ∃ I ∈ S, I ≤ P := by
  have h' := h
  rw [← hS.coe_toFinset, ← hS.toFinset.inf_id_eq_sInf] at h'
  obtain ⟨I, hI, hIP⟩ :=
    (inferInstance : P.IsPrime).inf_le'.mp h'
  exact ⟨I, hS.mem_toFinset.mp hI, hIP⟩

/-- If two nonempty finite families of prime ideals have all cross-component
intersections supported at the closed point, then the radical of the sum of
their intersections is the maximal ideal. -/
theorem radical_sup_sInf_eq_maximalIdeal_of_cross_zeroLocus
    {C : Type u} [CommRing C] [IsLocalRing C]
    {S T : Set (Ideal C)}
    (hSfinite : S.Finite) (hTfinite : T.Finite)
    (hSnonempty : S.Nonempty) (hTnonempty : T.Nonempty)
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hTprime : ∀ Q ∈ T, Q.IsPrime)
    (hcross : ∀ P ∈ S, ∀ Q ∈ T,
      PrimeSpectrum.zeroLocus P ∩ PrimeSpectrum.zeroLocus Q ⊆
        ({closedPoint C} : Set (PrimeSpectrum C))) :
    (sInf S ⊔ sInf T).radical = maximalIdeal C := by
  have hSle : sInf S ≤ maximalIdeal C := by
    obtain ⟨P, hPS⟩ := hSnonempty
    exact (sInf_le hPS).trans <|
      le_maximalIdeal (hSprime P hPS).ne_top
  have hTle : sInf T ≤ maximalIdeal C := by
    obtain ⟨Q, hQT⟩ := hTnonempty
    exact (sInf_le hQT).trans <|
      le_maximalIdeal (hTprime Q hQT).ne_top
  have hsup : sInf S ⊔ sInf T ≤ maximalIdeal C := sup_le hSle hTle
  apply le_antisymm
  · exact (maximalIdeal.isMaximal C).isPrime.radical_le_iff.mpr hsup
  · rw [Ideal.radical_eq_sInf, le_sInf_iff]
    intro K hK
    let : K.IsPrime := hK.2
    have hSK : sInf S ≤ K := le_sup_left.trans hK.1
    have hTK : sInf T ≤ K := le_sup_right.trans hK.1
    obtain ⟨P, hPS, hPK⟩ :=
      exists_mem_le_of_sInf_le_prime_of_finite hSfinite hSK
    obtain ⟨Q, hQT, hQK⟩ :=
      exists_mem_le_of_sInf_le_prime_of_finite hTfinite hTK
    let k : PrimeSpectrum C := ⟨K, inferInstance⟩
    have hk : k ∈
        PrimeSpectrum.zeroLocus P ∩ PrimeSpectrum.zeroLocus Q :=
      ⟨hPK, hQK⟩
    have hkclosed : k = closedPoint C :=
      Set.mem_singleton_iff.mp (hcross P hPS Q hQT hk)
    exact (congrArg PrimeSpectrum.asIdeal hkclosed).ge

/-- The previous reduction specialized to two finite subfamilies of the
minimal primes of an ideal in a Noetherian local ring. -/
theorem radical_sup_sInf_eq_maximalIdeal_of_minimalPrime_cross_zeroLocus
    {C : Type u} [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    (I : Ideal C) {S T : Set (Ideal C)}
    (hS : S ⊆ I.minimalPrimes) (hT : T ⊆ I.minimalPrimes)
    (hSnonempty : S.Nonempty) (hTnonempty : T.Nonempty)
    (hcross : ∀ P ∈ S, ∀ Q ∈ T,
      PrimeSpectrum.zeroLocus P ∩ PrimeSpectrum.zeroLocus Q ⊆
        ({closedPoint C} : Set (PrimeSpectrum C))) :
    (sInf S ⊔ sInf T).radical = maximalIdeal C := by
  exact radical_sup_sInf_eq_maximalIdeal_of_cross_zeroLocus
    (S := S) (T := T)
    ((I.finite_minimalPrimes_of_isNoetherianRing C).subset hS)
    ((I.finite_minimalPrimes_of_isNoetherianRing C).subset hT)
    hSnonempty hTnonempty
    (fun P hPS ↦ (hS hPS).isPrime)
    (fun Q hQT ↦ (hT hQT).isPrime)
    hcross

end AlgebraicGeometry.FiniteEtale

end
