/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ConnectedComponentFaithful
import Nyll.SchemeTheory.LocalGeometry.PuncturedSpectrum
import Nyll.SchemeTheory.RingTheory.PuncturedHypersurfacePrime
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Inseparable

/-!
# Faithful restriction from a neighbourhood of a punctured hypersurface

Let `U` be an open neighbourhood of the punctured hypersurface `V(f)` in the
spectrum of a Noetherian local ring. Only minimal primes lying in `U` and
outside `V(f)` need the quotient-dimension-at-least-two condition. Under that
condition, each connected component of `U` meets the hypersurface, and the
actual finite étale restriction functor is faithful.

This is the neighbourhood faithfulness implication of
[Stacks Project, Tag 0BLN](https://stacks.math.columbia.edu/tag/0BLN).
The existence of a suitable neighbourhood and the statement about the
colimit of neighbourhood categories are separate assertions.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace AlgebraicGeometry.FiniteEtale

/-- Every component of the neighbourhood meets the hypersurface if its
minimal primes outside the hypersurface have quotient dimension at least two.
The open need not itself be contained in the punctured spectrum. -/
theorem exists_hypersurface_point_in_neighborhood_connectedComponent
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (f : R) (hf : f ∈ maximalIdeal R)
    (U : (Spec (.of R)).Opens)
    (hzero : ∀ p : PrimeSpectrum R,
      p ∈ Scheme.puncturedSpectrumOpen R → f ∈ p.asIdeal → p ∈ U)
    (hdim : ∀ (P : Ideal R) (hP : P ∈ minimalPrimes R),
      (⟨P, hP.isPrime⟩ : PrimeSpectrum R) ∈ U → f ∉ P →
        (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P))
    (x : U) :
    ∃ y : U, f ∈ y.1.asIdeal ∧ y ∈ connectedComponent x := by
  have : x.1.asIdeal.IsPrime := x.1.isPrime
  obtain ⟨P, hP, hPx⟩ := Ideal.exists_minimalPrimes_le
    (bot_le : (⊥ : Ideal R) ≤ x.1.asIdeal)
  have : P.IsPrime := hP.isPrime
  let p₀ : PrimeSpectrum R := ⟨P, inferInstance⟩
  have hpx₀ : p₀ ⤳ x.1 :=
    (PrimeSpectrum.le_iff_specializes p₀ x.1).mp hPx
  have hpU : p₀ ∈ U := hpx₀.mem_open U.isOpen x.2
  let p : U := ⟨p₀, hpU⟩
  have hpx : p ⤳ x := (subtype_specializes_iff p x).mpr hpx₀
  have hxcomp : x ∈ connectedComponent p :=
    (closure_minimal (Set.singleton_subset_iff.mpr mem_connectedComponent)
      isClosed_connectedComponent) hpx.mem_closure
  by_cases hfP : f ∈ P
  · refine ⟨p, hfP, ?_⟩
    rw [← connectedComponent_eq hxcomp]
    exact mem_connectedComponent
  · obtain ⟨Q, hQ, hPQ, hfQ, hQne⟩ :=
      SchemeTheory.exists_prime_over_containing_ne_maximal_of_two_le_quotient_ringKrullDim
        R P (hdim P hP hpU hfP) f hf
    let q₀ : PrimeSpectrum R := ⟨Q, hQ⟩
    have hqpuncture : q₀ ∈ Scheme.puncturedSpectrumOpen R :=
      (Scheme.mem_puncturedSpectrumOpen_iff R q₀).mpr
        (fun h => hQne (congrArg PrimeSpectrum.asIdeal h))
    let q : U := ⟨q₀, hzero q₀ hqpuncture hfQ⟩
    have hpq : p ⤳ q := (subtype_specializes_iff p q).mpr
      ((PrimeSpectrum.le_iff_specializes p.1 q.1).mp hPQ)
    refine ⟨q, hfQ, ?_⟩
    rw [← connectedComponent_eq hxcomp]
    exact (closure_minimal (Set.singleton_subset_iff.mpr mem_connectedComponent)
      isClosed_connectedComponent) hpq.mem_closure

/-- Finite étale restriction from a neighbourhood of the punctured
hypersurface is faithful under the minimal-prime dimension hypothesis of
Stacks 58.22.1 (`0BLN`). The target is the literal pullback of `V(f)` to the
chosen open. In particular this applies to opens inside the puncture. -/
theorem pullback_faithful_punctured_hypersurface_neighborhood_of_minimalPrime_dimension
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (f : R) (hf : f ∈ maximalIdeal R)
    (U : (Spec (.of R)).Opens)
    (hzero : ∀ p : PrimeSpectrum R,
      p ∈ Scheme.puncturedSpectrumOpen R → f ∈ p.asIdeal → p ∈ U)
    (hdim : ∀ (P : Ideal R) (hP : P ∈ minimalPrimes R),
      (⟨P, hP.isPrime⟩ : PrimeSpectrum R) ∈ U → f ∉ P →
        (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P)) :
    (FiniteEtale.pullback (pullback.fst U.ι
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))))).Faithful := by
  let g := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
  apply pullback_faithful_of_meets_connectedComponents (pullback.fst U.ι g)
  intro x
  obtain ⟨y, hfy, hy⟩ :=
    exists_hypersurface_point_in_neighborhood_connectedComponent R f hf U hzero hdim x
  have hrange : U.ι y ∈ Set.range g := by
    change y.1 ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {f})))
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker]
    exact y.1.asIdeal.span_singleton_le_iff_mem.mpr hfy
  obtain ⟨z, hz⟩ := hrange
  obtain ⟨w, hwy, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := U.ι) (g := g) y z hz.symm
  exact ⟨w, hwy ▸ hy⟩

end AlgebraicGeometry.FiniteEtale
