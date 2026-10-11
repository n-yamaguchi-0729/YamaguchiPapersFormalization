/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.SpecialLocal.DimensionTwo.IntegralClosure.HeightTwo

/-!
# Purity for a normalization over a two-dimensional regular local ring

The full root cover used in the height-two Abhyankar argument, after the
selected divisor root has also been adjoined, is a regular local ring of
dimension two; it is not presented as a prime localization of a larger
regular ring.  This file supplies the corresponding intrinsic local-purity
endpoint.  The preceding conditional cover only classifies contractions of
height-one primes; purity is applied to the full cover.  Finiteness,
freeness, and a regular parameter pair are constructed from the local base,
so the only geometric input is etaleness at every height-one localization.
-/

noncomputable section

namespace EtaleFundamentalGroups.SpecialLocalPurity

open IsLocalRing

universe u v w

/-- A normalization in a finite separable extension of the fraction field of
an arbitrary two-dimensional regular local domain is etale once all of its
height-one localizations are etale.  In the height-two Abhyankar consumer,
the local domain is the full selected-root cover, not the preceding
conditional cover.

The normalization is proved finite and free internally, and the required
regular parameter pair is lifted from the cotangent space. -/
theorem integralClosure_etale_of_isRegularLocalRing_dimension_two
    {A : Type u} {K : Type v} {L : Type w}
    [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hdim : ringKrullDim A = ((2 : ℕ∞) : WithBot ℕ∞))
    (hlocal : ∀ (q : Ideal A) [q.IsPrime], q.height = 1 →
      Algebra.Etale (Localization.AtPrime q)
        (Localization (Algebra.algebraMapSubmonoid
          (integralClosure A L) q.primeCompl))) :
    Algebra.Etale A (integralClosure A L) := by
  let : Module.Finite A (integralClosure A L) :=
    integralClosure_finite_of_isRegularLocalRing_dimension_two
      (K := K) hdim
  let : Module.Free A (integralClosure A L) :=
    integralClosure_free_of_isRegularLocalRing_dimension_two
      (K := K) hdim
  have hfin :
      Module.finrank (IsLocalRing.ResidueField A) (CotangentSpace A) = 2 := by
    have hreg :=
      (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance
    rw [hdim] at hreg
    exact ENat.natCast_inj.mp (WithBot.coe_eq_coe.mp hreg)
  obtain ⟨x, y, hregular, hspan⟩ :=
    EtaleFundamentalGroups.exists_regular_pair_of_finrank_cotangentSpace_eq_two_unconstrained
      hfin hdim
  exact etale_of_regular_pair_of_etale_localizationAtPrime
    hregular hspan hlocal

end EtaleFundamentalGroups.SpecialLocalPurity

end
