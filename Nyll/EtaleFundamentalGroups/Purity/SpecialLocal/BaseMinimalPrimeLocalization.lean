/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.SpecialLocal.BaseMinimalPrime
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Localizing at a minimal non-etale base point

Let `p` be minimal in the base support of the two cotangent obstructions for
a finite algebra `S` over `R`.  After localizing both rings at the complement
of `p`, every target prime away from the fibre over the closed point is
etale over `R_p`.
-/

noncomputable section

namespace EtaleFundamentalGroups.SpecialLocalPurity

universe u v

/-- After localizing a finite algebra at a minimal bad base point, every
target prime not lying over the closed point is etale.  The target prime is
contracted through the prime-localization correspondence, where its base
contraction becomes strictly smaller than the chosen minimal point. -/
theorem
    localizedFiniteAlgebra_isEtaleAt_away_from_closedPoint_of_minimal_base_nonEtaleCotangentSupport
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S]
    (p : PrimeSpectrum R)
    (hp : Minimal
      (· ∈ Module.support R Ω[S⁄R] ∪
        Module.support R (Algebra.H1Cotangent R S)) p)
    (Q : PrimeSpectrum
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))
    (hQ :
      PrimeSpectrum.comap
          (algebraMap (Localization.AtPrime p.asIdeal)
            (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))) Q ≠
        ⟨IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal), inferInstance⟩) :
    Algebra.IsEtaleAt (Localization.AtPrime p.asIdeal) Q.asIdeal := by
  let Rₚ := Localization.AtPrime p.asIdeal
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let q : PrimeSpectrum Rₚ :=
    PrimeSpectrum.comap (algebraMap Rₚ Sₚ) Q
  let closed : PrimeSpectrum Rₚ :=
    ⟨IsLocalRing.maximalIdeal Rₚ, inferInstance⟩
  have hqne : q ≠ closed := hQ
  have hqle : q ≤ closed :=
    IsLocalRing.le_maximalIdeal q.isPrime.ne_top
  have hqunder_le : q.asIdeal.under R ≤ p.asIdeal := by
    calc
      q.asIdeal.under R ≤
          (IsLocalRing.maximalIdeal Rₚ).under R := Ideal.comap_mono hqle
      _ = p.asIdeal := Localization.AtPrime.under_maximalIdeal
  have hqunder_ne : q.asIdeal.under R ≠ p.asIdeal := by
    intro h
    have hmax : q.asIdeal = IsLocalRing.maximalIdeal Rₚ :=
      Localization.AtPrime.eq_maximalIdeal_iff_under_eq.mp h
    exact hqne (PrimeSpectrum.ext hmax)
  have hqunder_lt : q.asIdeal.under R < p.asIdeal :=
    lt_of_le_of_ne hqunder_le hqunder_ne
  let P : PrimeSpectrum S :=
    PrimeSpectrum.comap (algebraMap S Sₚ) Q
  have hP_lt : PrimeSpectrum.comap (algebraMap R S) P < p := by
    change (PrimeSpectrum.comap (algebraMap R S) P).asIdeal < p.asIdeal
    rw [show (PrimeSpectrum.comap (algebraMap R S) P).asIdeal =
        q.asIdeal.under R by
      ext r
      simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      change algebraMap S Sₚ (algebraMap R S r) ∈ Q.asIdeal ↔
        algebraMap Rₚ Sₚ (algebraMap R Rₚ r) ∈ Q.asIdeal
      rw [← IsScalarTower.algebraMap_apply R S Sₚ,
        ← IsScalarTower.algebraMap_apply R Rₚ Sₚ]]
    exact hqunder_lt
  have hEtale : Algebra.IsEtaleAt R P.asIdeal :=
    isEtaleAt_of_comap_lt_minimal_base_nonEtaleCotangentSupport p hp P hP_lt
  let : Algebra.FormallyEtale R (Localization.AtPrime P.asIdeal) := hEtale
  let e : Localization.AtPrime P.asIdeal ≃ₐ[S] Localization.AtPrime Q.asIdeal :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) Q.asIdeal
  let : Algebra.FormallyEtale R (Localization.AtPrime Q.asIdeal) :=
    Algebra.FormallyEtale.of_equiv (e.restrictScalars R)
  exact Algebra.FormallyEtale.localization_base p.asIdeal.primeCompl

end EtaleFundamentalGroups.SpecialLocalPurity

end
