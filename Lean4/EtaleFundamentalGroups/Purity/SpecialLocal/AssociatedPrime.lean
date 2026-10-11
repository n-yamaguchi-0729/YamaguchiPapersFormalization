/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.SpecialLocal.CotangentFinite
import EtaleFundamentalGroups.Purity.SpecialLocal.Support

/-!
# Minimal cotangent support and associated primes

For a finite module over a Noetherian ring, a minimal point of its support is
an associated prime.  Applying this to the two finite cotangent modules turns
a minimal point of the non-etale cotangent support into an associated prime of
one of those modules.  The codimension-one hypothesis from
`SpecialLocalPuritySupport` simultaneously shows that this prime does not have
height one.

This is the exact interface at which a depth or branch-locus theorem must
enter; no height bound or purity conclusion is assumed here.
-/

noncomputable section

namespace EtaleFundamentalGroups.SpecialLocalPurity

universe u v

/-- A minimal point of the support of a finite module is a minimal prime over
its annihilator. -/
theorem mem_minimalPrimes_annihilator_of_minimal_mem_support
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (P : PrimeSpectrum R)
    (hP : Minimal (· ∈ Module.support R M) P) :
    P.asIdeal ∈ (Module.annihilator R M).minimalPrimes := by
  refine ⟨⟨P.isPrime, Module.mem_support_iff_of_finite.mp hP.1⟩, ?_⟩
  intro q hq hqP
  let Q : PrimeSpectrum R := ⟨q, hq.1⟩
  have hQSupport : Q ∈ Module.support R M :=
    Module.mem_support_iff_of_finite.mpr hq.2
  exact hP.2 hQSupport hqP

/-- A minimal point of the support of a finite module over a Noetherian ring
is an associated prime. -/
theorem mem_associatedPrimes_of_minimal_mem_support
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] (P : PrimeSpectrum R)
    (hP : Minimal (· ∈ Module.support R M) P) :
    P.asIdeal ∈ associatedPrimes R M :=
  Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M
    (mem_minimalPrimes_annihilator_of_minimal_mem_support P hP)

/-- If a finite algebra is not formally etale, the union of its two
cotangent supports has a minimal point.  The point is obtained from a
minimal prime over the intersection of the two annihilator ideals, so no
Noetherian topological choice is hidden in the statement. -/
theorem exists_minimal_nonEtaleCotangentSupport_of_not_formallyEtale
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [Algebra R S] [Module.Finite R S]
    (hne : ¬ Algebra.FormallyEtale R S) :
    ∃ P : PrimeSpectrum S,
      Minimal
        (· ∈ Module.support S Ω[S⁄R] ∪
          Module.support S (Algebra.H1Cotangent R S)) P := by
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let : Module.Finite S Ω[S⁄R] :=
    kaehlerDifferential_finite_of_finite_over_noetherian
  let : Module.Finite S (Algebra.H1Cotangent R S) :=
    h1Cotangent_finite_of_finite_over_noetherian
  let T :=
    Module.support S Ω[S⁄R] ∪
      Module.support S (Algebra.H1Cotangent R S)
  have hT : T.Nonempty := by
    by_contra hempty
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    apply hne
    rw [← Algebra.etaleLocus_eq_univ_iff]
    rw [Algebra.etaleLocus_eq_compl_support]
    have hΩ : Module.support S Ω[S⁄R] = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro P hP
      have : P ∈ T := Or.inl hP
      rw [hTempty] at this
      exact Set.notMem_empty P this
    have hH1 : Module.support S (Algebra.H1Cotangent R S) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro P hP
      have : P ∈ T := Or.inr hP
      rw [hTempty] at this
      exact Set.notMem_empty P this
    rw [hΩ, hH1]
    simp
  obtain ⟨P₀, hP₀⟩ := hT
  let IΩ := Module.annihilator S Ω[S⁄R]
  let IH1 := Module.annihilator S (Algebra.H1Cotangent R S)
  let J : Ideal S := IΩ ⊓ IH1
  have hJleP₀ : J ≤ P₀.asIdeal := by
    rcases hP₀ with hP₀ | hP₀
    · exact inf_le_left.trans
        (Module.mem_support_iff_of_finite.mp hP₀)
    · exact inf_le_right.trans
        (Module.mem_support_iff_of_finite.mp hP₀)
  have hJne : J ≠ ⊤ :=
    ne_top_of_le_ne_top P₀.isPrime.ne_top hJleP₀
  obtain ⟨p, hp⟩ := J.nonempty_minimalPrimes hJne
  let P : PrimeSpectrum S := ⟨p, hp.isPrime⟩
  have hIp : IΩ ≤ p ∨ IH1 ≤ p := by
    apply hp.isPrime.inf_le.mp
    simpa only [J] using hp.le
  have hPsupport : P ∈ T := by
    rcases hIp with hIp | hIp
    · exact Or.inl (Module.mem_support_iff_of_finite.mpr hIp)
    · exact Or.inr (Module.mem_support_iff_of_finite.mpr hIp)
  refine ⟨P, hPsupport, ?_⟩
  intro Q hQsupport hQP
  have hJQ : J ≤ Q.asIdeal := by
    rcases hQsupport with hQ | hQ
    · exact inf_le_left.trans
        (Module.mem_support_iff_of_finite.mp hQ)
    · exact inf_le_right.trans
        (Module.mem_support_iff_of_finite.mp hQ)
  exact hp.2 ⟨Q.isPrime, hJQ⟩ hQP

/-- Every prime strictly below a minimal point of the non-etale cotangent
support lies in the etale locus. -/
theorem isEtaleAt_of_lt_minimal_nonEtaleCotangentSupport
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S]
    (P : PrimeSpectrum S)
    (hP : Minimal
      (· ∈ Module.support S Ω[S⁄R] ∪
        Module.support S (Algebra.H1Cotangent R S)) P)
    (Q : PrimeSpectrum S) (hQP : Q < P) :
    Algebra.IsEtaleAt R Q.asIdeal := by
  change Q ∈ Algebra.etaleLocus R S
  rw [Algebra.etaleLocus_eq_compl_support]
  constructor
  · intro hQ
    exact (not_le_of_gt hQP) (hP.2 (Or.inl hQ) hQP.le)
  · intro hQ
    exact (not_le_of_gt hQP) (hP.2 (Or.inr hQ) hQP.le)

/-- Under height-one etaleness, a minimal point of the non-etale cotangent
support is an associated prime of one cotangent module and is not height one.
This packages the two production inputs without assuming the missing purity
height bound. -/
theorem minimal_nonEtaleCotangentSupport_associated_and_height_ne_one
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] [IsDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    (hetale :
      ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
        ∀ (P : Ideal S) [P.IsPrime] [P.LiesOver p],
          Algebra.IsEtaleAt R P)
    (P : PrimeSpectrum S)
    (hP : Minimal
      (· ∈ Module.support S Ω[S⁄R] ∪
        Module.support S (Algebra.H1Cotangent R S)) P) :
    P.asIdeal ∈ associatedPrimes S Ω[S⁄R] ∪
        associatedPrimes S (Algebra.H1Cotangent R S) ∧
      P.asIdeal.height ≠ 1 := by
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let : Module.Finite S Ω[S⁄R] :=
    kaehlerDifferential_finite_of_finite_over_noetherian
  let : Module.Finite S (Algebra.H1Cotangent R S) :=
    h1Cotangent_finite_of_finite_over_noetherian
  constructor
  · rcases hP.1 with hΩ | hH1
    · left
      apply mem_associatedPrimes_of_minimal_mem_support P
      exact ⟨hΩ, fun Q hQ hQP ↦ hP.2 (Or.inl hQ) hQP⟩
    · right
      apply mem_associatedPrimes_of_minimal_mem_support P
      exact ⟨hH1, fun Q hQ hQP ↦ hP.2 (Or.inr hQ) hQP⟩
  · exact
      nonEtaleCotangentSupport_subset_height_ne_one_of_isEtaleAt_heightOne hetale hP.1

/-- A non-formally-etale finite torsion-free domain extension which is
etale over every height-one prime has a higher-codimension associated
cotangent prime.  This is the contradiction witness used by the
minimal-bad-point branch-locus argument. -/
theorem
    exists_nonEtaleCotangentSupport_associated_and_height_ne_one_of_isEtaleAt_heightOne
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] [IsDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    (hetale :
      ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
        ∀ (P : Ideal S) [P.IsPrime] [P.LiesOver p],
          Algebra.IsEtaleAt R P)
    (hne : ¬ Algebra.FormallyEtale R S) :
    ∃ P : PrimeSpectrum S,
      P.asIdeal ∈ associatedPrimes S Ω[S⁄R] ∪
          associatedPrimes S (Algebra.H1Cotangent R S) ∧
        P.asIdeal.height ≠ 1 := by
  obtain ⟨P, hP⟩ :=
    exists_minimal_nonEtaleCotangentSupport_of_not_formallyEtale hne
  exact ⟨P,
    minimal_nonEtaleCotangentSupport_associated_and_height_ne_one
      hetale P hP⟩

end EtaleFundamentalGroups.SpecialLocalPurity

end
