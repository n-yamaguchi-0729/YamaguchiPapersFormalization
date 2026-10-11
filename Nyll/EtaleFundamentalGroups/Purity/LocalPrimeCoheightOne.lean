/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.HartshorneLichtenbaumReduction
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# A one-dimensional prime quotient over a nonmaximal radical

A proper ideal with nonmaximal radical lies in a nonmaximal prime.  The
spectrum of a Noetherian local ring has finite dimension, so a prime of
coheight one lies above that prime.  The quotient-spectrum order
isomorphism identifies its coheight with the dimension of its quotient.
-/

namespace EtaleFundamentalGroups.Purity

universe u

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A proper ideal whose radical is not maximal is contained in a
nonmaximal prime with one-dimensional quotient. -/
theorem exists_prime_over_lt_maximalIdeal_with_quotient_dim_one
    (I : Ideal R) (hI : I ≠ ⊤) (hradical : I.radical ≠ maximalIdeal R) :
    ∃ P : Ideal R, I ≤ P ∧ P.IsPrime ∧ P < maximalIdeal R ∧
      ringKrullDim (R ⧸ P) = (1 : WithBot ℕ∞) := by
  obtain ⟨P, hIP, hP, hPm⟩ :=
    EtaleFundamentalGroups.exists_prime_over_lt_maximalIdeal_of_radical_ne I hI hradical
  let p : PrimeSpectrum R := ⟨P, hP⟩
  have hptop : p < ⊤ := hPm
  have hone : (1 : ℕ∞) ≤ Order.coheight p := by
    simpa only [Order.coheight_top, zero_add] using Order.coheight_add_one_le hptop
  have hex : ∃ q : PrimeSpectrum R, p ≤ q ∧ Order.coheight q = 1 := by
    by_cases hpone : Order.coheight p = 1
    · exact ⟨p, le_rfl, hpone⟩
    · have hlt : (1 : ℕ∞) < Order.coheight p := lt_of_le_of_ne hone (Ne.symm hpone)
      obtain ⟨q, hpq, hq⟩ :=
        (Order.coe_lt_coheight_iff (n := 1) (Order.coheight_lt_top p)).mp hlt
      exact ⟨q, hpq.le, hq⟩
  obtain ⟨q, hpq, hq⟩ := hex
  have hqne : q ≠ ⊤ := by
    intro hqtop
    rw [hqtop, Order.coheight_top] at hq
    exact zero_ne_one hq
  have hqm : q.asIdeal < maximalIdeal R :=
    (lt_top_iff_ne_top.mpr hqne : q < ⊤)
  refine ⟨q.asIdeal, hIP.trans hpq, q.isPrime, hqm, ?_⟩
  calc
    ringKrullDim (R ⧸ q.asIdeal) =
        Order.krullDim (PrimeSpectrum.zeroLocus (R := R) q.asIdeal) :=
      Order.krullDim_eq_of_orderIso q.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus
    _ = (Order.coheight q : WithBot ℕ∞) := (Order.coheight_eq_krullDim_Ici q).symm
    _ = 1 := congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hq

end EtaleFundamentalGroups.Purity
