/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.HartshorneLichtenbaumReduction
import EtaleFundamentalGroups.Purity.PuncturedSpectrum
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Finite dimension and the geometric Hartshorne--Lichtenbaum frontier

Finite Krull dimension gives an actual natural-number dimension, rather
than only a `WithBot ENat` value.  We also record the geometric content of
a proper radical support being different from the maximal ideal: its closed
set contains a point of the punctured spectrum.
-/

noncomputable section

open IsLocalRing TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- The Krull dimension of a ring with finite Krull dimension is represented
by a natural number.  In particular this applies to every Noetherian local
ring via Mathlib's `FiniteRingKrullDim` instance. -/
theorem exists_nat_ringKrullDim_eq_of_finiteRingKrullDim
    {R : Type u} [CommRing R] [FiniteRingKrullDim R] :
    ∃ d : ℕ, ringKrullDim R = (d : WithBot ℕ∞) := by
  obtain ⟨e, he⟩ :=
    WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := R))
  have hetop : e ≠ ⊤ := by
    intro heTop
    apply ringKrullDim_ne_top (R := R)
    rw [← he, heTop, WithBot.coe_top]
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hetop
  refine ⟨d, ?_⟩
  calc
    ringKrullDim R = (e : WithBot ℕ∞) := he.symm
    _ = ((d : ℕ∞) : WithBot ℕ∞) :=
      congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hd.symm

/-- A proper radical ideal different from the maximal ideal is contained in
a nonmaximal prime.  The explicit properness hypothesis is necessary: the
unit ideal is radical and differs from the maximal ideal. -/
theorem exists_nonmaximal_prime_over_of_isRadical
    {R : Type u} [CommRing R] [IsLocalRing R]
    (J : Ideal R) (hJradical : J.IsRadical)
    (hJproper : J ≠ ⊤) (hJnonmax : J ≠ maximalIdeal R) :
    ∃ P : Ideal R,
      J ≤ P ∧ P.IsPrime ∧ P ≠ maximalIdeal R := by
  have hradical : J.radical ≠ maximalIdeal R := by
    simpa only [hJradical.radical] using hJnonmax
  obtain ⟨P, hJP, hPprime, hPlt⟩ :=
    EtaleFundamentalGroups.exists_prime_over_lt_maximalIdeal_of_radical_ne
      J hJproper hradical
  exact ⟨P, hJP, hPprime, hPlt.ne⟩

/-- The zero locus of a proper radical nonmaximal ideal meets the punctured
spectrum. -/
theorem zeroLocus_inter_puncture_nonempty_of_isRadical
    {R : Type u} [CommRing R] [IsLocalRing R]
    (J : Ideal R) (hJradical : J.IsRadical)
    (hJproper : J ≠ ⊤) (hJnonmax : J ≠ maximalIdeal R) :
    (PrimeSpectrum.zeroLocus J ∩
      ({closedPoint R}ᶜ : Set (PrimeSpectrum R))).Nonempty := by
  obtain ⟨P, hJP, hPprime, hPnonmax⟩ :=
    exists_nonmaximal_prime_over_of_isRadical
      J hJradical hJproper hJnonmax
  let p : PrimeSpectrum R := ⟨P, hPprime⟩
  have hpnonmax : p ≠ closedPoint R := by
    intro hp
    apply hPnonmax
    exact congrArg PrimeSpectrum.asIdeal hp
  exact ⟨p, hJP, by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hpnonmax⟩

end AlgebraicGeometry.FiniteEtale

end
