/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.UnramifiedNormalBase
import SchemeTheory.RingTheory.Descent.FiniteUnramifiedNeighborhood
import SchemeTheory.RingTheory.Descent.EtalePrimeLocalization
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Étale neighborhoods of finite domain models over a normal domain

Opening the unramified locus first avoids assuming finite presentation or
Noetherianity. The dominant-domain criterion supplies étaleness afterwards.
This is the spreading step for the original local criterion in Tag 0BTF.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u

/-- A finite domain faithful over a normal domain which becomes étale after
localizing the base at a prime is étale on a principal neighborhood of that
prime. No finite presentation or Noetherian assumption is needed. -/
theorem exists_etale_away_of_finite_domain_localized_etale
    {R C : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing C] [IsDomain C] [Algebra R C] [FaithfulSMul R C] [Module.Finite R C]
    (p : PrimeSpectrum R)
    (hEtale : Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid C p.asIdeal.primeCompl))) :
    ∃ r : R, r ∉ p.asIdeal ∧ Algebra.Etale R (Localization.Away (algebraMap R C r)) := by
  obtain ⟨r, hr, hunramified⟩ :=
    SchemeTheory.exists_unramified_away_of_isUnramifiedAt_fiber p (by
      intro P hPp
      have : Algebra.IsEtaleAt R P.asIdeal :=
        SchemeTheory.isEtaleAt_of_localizedAlgebra_etale p hEtale P hPp
      infer_instance)
  let Cr := Localization.Away (algebraMap R C r)
  have hrzero : r ≠ 0 := fun h => hr (h ▸ p.asIdeal.zero_mem)
  have hCzero : algebraMap R C r ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R C)).mpr hrzero
  have : IsDomain Cr := Localization.Away.isDomain hCzero
  have : FaithfulSMul R Cr :=
    (faithfulSMul_iff_algebraMap_injective R Cr).mpr <| by
      rw [IsScalarTower.algebraMap_eq R C Cr]
      exact (IsLocalization.injective Cr
        (powers_le_nonZeroDivisors_of_noZeroDivisors hCzero)).comp
          (FaithfulSMul.algebraMap_injective R C)
  have : Algebra.FormallyUnramified R Cr := hunramified
  exact ⟨r, hr, etale_of_unramified_of_domain_of_faithful⟩

end EtaleFundamentalGroups
