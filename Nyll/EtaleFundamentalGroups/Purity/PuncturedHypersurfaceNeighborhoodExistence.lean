/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedHypersurfaceNeighborhoodFaithful
import Nyll.SchemeTheory.LocalGeometry.PuncturedSpectrum
import Nyll.SchemeTheory.RingTheory.PrimeContainingAtHeightOne
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Basic

/-!
# Neighbourhoods with faithful restriction to the punctured hypersurface

Delete the closed sets of the minimal primes outside `V(f)` whose quotient
dimension is less than two. There are finitely many such primes. None of
those closed sets meets the punctured hypersurface: such an intersection
would provide a strict chain of two primes in the corresponding quotient.

The remaining open inside the puncture contains the punctured hypersurface
and satisfies the minimal-prime dimension condition. Every smaller open
containing the same hypersurface also satisfies that condition, so finite
étale restriction is faithful for all of them.

This proves the neighbourhood-existence assertion in
[Stacks Project, Tag 0BLN](https://stacks.math.columbia.edu/tag/0BLN).
The categorical-colimit assertion is a separate statement.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace AlgebraicGeometry.FiniteEtale

/-- There is an open neighbourhood of the punctured hypersurface, contained
in the puncture, for which all minimal primes outside the hypersurface have
quotient dimension at least two. It is obtained by deleting finitely many
closed subsets belonging to the other minimal primes. -/
theorem exists_punctured_hypersurface_neighborhood_minimalPrime_dimension
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (f : R) :
    ∃ U : (Spec (.of R)).Opens,
      U ≤ Scheme.puncturedSpectrumOpen R ∧
      (∀ p : PrimeSpectrum R,
        p ∈ Scheme.puncturedSpectrumOpen R → f ∈ p.asIdeal → p ∈ U) ∧
      (∀ (P : Ideal R) (hP : P ∈ minimalPrimes R),
        (⟨P, hP.isPrime⟩ : PrimeSpectrum R) ∈ U → f ∉ P →
          (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P)) := by
  classical
  let bad : Set (Ideal R) :=
    {P | P ∈ minimalPrimes R ∧ f ∉ P ∧
      ¬ (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P)}
  have hbadFinite : bad.Finite :=
    (minimalPrimes.finite_of_isNoetherianRing R).subset (fun P hP => hP.1)
  let Z : Set (PrimeSpectrum R) :=
    ⋃ P ∈ bad, PrimeSpectrum.zeroLocus (P : Set R)
  have hZClosed : IsClosed Z :=
    hbadFinite.isClosed_biUnion
      (fun P _ => PrimeSpectrum.isClosed_zeroLocus (P : Set R))
  let U : (Spec (.of R)).Opens :=
    Scheme.puncturedSpectrumOpen R ⊓ ⟨Zᶜ, hZClosed.isOpen_compl⟩
  refine ⟨U, inf_le_left, ?_, ?_⟩
  · intro q hqpuncture hfq
    change q ∈ Scheme.puncturedSpectrumOpen R ∧ q ∉ Z
    refine ⟨hqpuncture, ?_⟩
    intro hqZ
    obtain ⟨P, hqP⟩ := Set.mem_iUnion.mp hqZ
    obtain ⟨hPbad, hPQ⟩ := Set.mem_iUnion.mp hqP
    have hPminimal : P ∈ minimalPrimes R := hPbad.1
    have hfP : f ∉ P := hPbad.2.1
    have hdimP : ¬ (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P) := hPbad.2.2
    have : P.IsPrime := hPminimal.isPrime
    have : q.asIdeal.IsPrime := q.isPrime
    have hPQle : P ≤ q.asIdeal :=
      (PrimeSpectrum.mem_zeroLocus q (P : Set R)).mp hPQ
    have hPQlt : P < q.asIdeal :=
      lt_of_le_of_ne hPQle (fun h => hfP (h.symm ▸ hfq))
    have hqmNe : q.asIdeal ≠ maximalIdeal R := by
      intro h
      exact (Scheme.mem_puncturedSpectrumOpen_iff R q).mp hqpuncture
        (PrimeSpectrum.ext h)
    have hqm : q.asIdeal < maximalIdeal R :=
      lt_of_le_of_ne (le_maximalIdeal q.isPrime.ne_top) hqmNe
    exact hdimP (SchemeTheory.two_le_quotient_dimension_of_prime_chain
      P q.asIdeal hPQlt hqm)
  · intro P hP hpU hfP
    by_contra hdimP
    have hPbad : P ∈ bad := ⟨hP, hfP, hdimP⟩
    have hpZ : (⟨P, hP.isPrime⟩ : PrimeSpectrum R) ∈ Z :=
      Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hPbad,
        (PrimeSpectrum.mem_zeroLocus _ (P : Set R)).mpr (fun _ hx => hx)⟩⟩
    change (⟨P, hP.isPrime⟩ : PrimeSpectrum R) ∈ Scheme.puncturedSpectrumOpen R ∧
      (⟨P, hP.isPrime⟩ : PrimeSpectrum R) ∉ Z at hpU
    exact hpU.2 hpZ

/-- A punctured hypersurface admits a neighbourhood on which finite étale
restriction is faithful, and faithfulness persists for every smaller open
neighbourhood. This uses only the original Noetherian local hypotheses and
an equation in the maximal ideal. -/
theorem exists_punctured_hypersurface_neighborhood_faithful
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (f : R) (hf : f ∈ maximalIdeal R) :
    ∃ U : (Spec (.of R)).Opens,
      U ≤ Scheme.puncturedSpectrumOpen R ∧
      (∀ p : PrimeSpectrum R,
        p ∈ Scheme.puncturedSpectrumOpen R → f ∈ p.asIdeal → p ∈ U) ∧
      (∀ V : (Spec (.of R)).Opens, V ≤ U →
        (∀ p : PrimeSpectrum R,
          p ∈ Scheme.puncturedSpectrumOpen R → f ∈ p.asIdeal → p ∈ V) →
        (FiniteEtale.pullback (pullback.fst V.ι
          (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (Ideal.span {f})))))).Faithful) := by
  obtain ⟨U, hUpuncture, hUzero, hUdim⟩ :=
    exists_punctured_hypersurface_neighborhood_minimalPrime_dimension R f
  refine ⟨U, hUpuncture, hUzero, ?_⟩
  intro V hVU hVzero
  apply pullback_faithful_punctured_hypersurface_neighborhood_of_minimalPrime_dimension
    R f hf V hVzero
  intro P hP hpV hfP
  exact hUdim P hP (hVU hpV) hfP

end AlgebraicGeometry.FiniteEtale
