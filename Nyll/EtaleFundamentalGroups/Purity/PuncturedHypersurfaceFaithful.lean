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

/-!
# Faithful restriction to a punctured hypersurface

If every minimal prime not containing the equation has quotient dimension
at least two, every connected component of the punctured spectrum meets the
hypersurface. Consequently finite étale restriction to its actual pullback
is faithful. This proves the dimension case of Stacks 58.19.2 (`0BLG`);
its component-intersection case is the general connected-component theorem.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace AlgebraicGeometry.FiniteEtale

/-- The dimension condition on minimal primes forces the hypersurface to
meet each connected component of the puncture. -/
theorem exists_hypersurface_point_in_connectedComponent_of_minimalPrime_dimension
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (f : R) (hf : f ∈ maximalIdeal R)
    (hdim : ∀ P ∈ minimalPrimes R, f ∉ P →
      (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P))
    (x : Scheme.puncturedSpectrum R) :
    ∃ y : Scheme.puncturedSpectrum R,
      f ∈ y.1.asIdeal ∧ y ∈ connectedComponent x := by
  have : x.1.asIdeal.IsPrime := x.1.isPrime
  obtain ⟨P, hP, hPx⟩ := Ideal.exists_minimalPrimes_le
    (bot_le : (⊥ : Ideal R) ≤ x.1.asIdeal)
  have : P.IsPrime := hP.isPrime
  have hPne : P ≠ maximalIdeal R := by
    intro hPm
    have hx : x.1.asIdeal = maximalIdeal R :=
      le_antisymm (le_maximalIdeal x.1.isPrime.ne_top) (hPm ▸ hPx)
    exact (Scheme.mem_puncturedSpectrumOpen_iff R x.1).mp x.2
      (PrimeSpectrum.ext hx)
  let p : Scheme.puncturedSpectrum R :=
    ⟨⟨P, inferInstance⟩, (Scheme.mem_puncturedSpectrumOpen_iff R _).mpr
      (fun h => hPne (congrArg PrimeSpectrum.asIdeal h))⟩
  have hpx : p ⤳ x := (subtype_specializes_iff p x).mpr
    ((PrimeSpectrum.le_iff_specializes p.1 x.1).mp hPx)
  have hxcomp : x ∈ connectedComponent p :=
    (closure_minimal (Set.singleton_subset_iff.mpr mem_connectedComponent)
      isClosed_connectedComponent) hpx.mem_closure
  by_cases hfP : f ∈ P
  · refine ⟨p, hfP, ?_⟩
    rw [← connectedComponent_eq hxcomp]
    exact mem_connectedComponent
  · obtain ⟨Q, hQ, hPQ, hfQ, hQne⟩ :=
      SchemeTheory.exists_prime_over_containing_ne_maximal_of_two_le_quotient_ringKrullDim
        R P (hdim P hP hfP) f hf
    let q : Scheme.puncturedSpectrum R :=
      ⟨⟨Q, hQ⟩, (Scheme.mem_puncturedSpectrumOpen_iff R _).mpr
        (fun h => hQne (congrArg PrimeSpectrum.asIdeal h))⟩
    have hpq : p ⤳ q := (subtype_specializes_iff p q).mpr
      ((PrimeSpectrum.le_iff_specializes p.1 q.1).mp hPQ)
    refine ⟨q, hfQ, ?_⟩
    rw [← connectedComponent_eq hxcomp]
    exact (closure_minimal (Set.singleton_subset_iff.mpr mem_connectedComponent)
      isClosed_connectedComponent) hpq.mem_closure

/-- Finite étale restriction to the punctured hypersurface is faithful under
the minimal-prime dimension condition of Stacks 58.19.2 (`0BLG`). The source
of the restriction is the literal scheme pullback defining that hypersurface. -/
theorem pullback_faithful_punctured_hypersurface_of_minimalPrime_dimension
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (f : R) (hf : f ∈ maximalIdeal R)
    (hdim : ∀ P ∈ minimalPrimes R, f ∉ P →
      (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P)) :
    (FiniteEtale.pullback (pullback.fst (Scheme.puncturedSpectrumInclusion R)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))))).Faithful := by
  let j := Scheme.puncturedSpectrumInclusion R
  let g := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
  apply pullback_faithful_of_meets_connectedComponents (pullback.fst j g)
  intro x
  obtain ⟨y, hfy, hy⟩ :=
    exists_hypersurface_point_in_connectedComponent_of_minimalPrime_dimension R f hf hdim x
  have hrange : j y ∈ Set.range g := by
    change y.1 ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {f})))
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker]
    exact y.1.asIdeal.span_singleton_le_iff_mem.mpr hfy
  obtain ⟨z, hz⟩ := hrange
  obtain ⟨w, hwy, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := j) (g := g) y z hz.symm
  exact ⟨w, hwy ▸ hy⟩

end AlgebraicGeometry.FiniteEtale
