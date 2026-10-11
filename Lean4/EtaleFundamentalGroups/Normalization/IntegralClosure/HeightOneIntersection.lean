/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.Tower
import Mathlib.RingTheory.Polynomial.RationalRoot
import EtaleFundamentalGroups.Purity.HeightOne.UFDIntersection

/-!
# Integral elements detected at the height-one points of a UFD

For a finite algebraic extension of the fraction field of a UFD, an element
which is integral over every localization at a prime element is already
integral over the UFD.  We descend the coefficients of its minimal polynomial
using `mem_bot_of_mem_localization_primeElement`.

This is the codimension-one intersection theorem for the normalization that
is needed in the two-dimensional local-purity argument.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u v w

/-- Integrality over a UFD is detected by the localizations at its prime
elements, for elements in an algebraic extension of the fraction field. -/
theorem isIntegral_of_isIntegral_localization_primeElement
    {A : Type u} {K : Type v} {L : Type w}
    [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [Algebra.IsAlgebraic K L]
    (z : L)
    (hz : ∀ (p : A) (hp : Prime p),
      letI : (Ideal.span {p}).IsPrime :=
        Ideal.isPrime_span_singleton_of_prime hp
      let Aₚ := Localization.subalgebra.ofField K (Ideal.span {p}).primeCompl
        (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {p}))
      IsIntegral Aₚ z) :
    IsIntegral A z := by
  have hcoeff : ∀ i : ℕ, (minpoly K z).coeff i ∈ (algebraMap A K).range := by
    intro i
    apply Algebra.mem_bot.mp
    apply mem_bot_of_mem_localization_primeElement (z := (minpoly K z).coeff i)
    intro p hp
    let : (Ideal.span {p}).IsPrime :=
      Ideal.isPrime_span_singleton_of_prime hp
    let Aₚ := Localization.subalgebra.ofField K (Ideal.span {p}).primeCompl
      (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {p}))
    let : IsIntegrallyClosed Aₚ :=
      isIntegrallyClosed_of_isLocalization Aₚ (Ideal.span {p}).primeCompl
        (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {p}))
    have hzₚ : IsIntegral Aₚ z := hz p hp
    have hmin := minpoly.isIntegrallyClosed_eq_field_fractions' K hzₚ
    rw [hmin, Polynomial.coeff_map]
    exact Subtype.prop _
  obtain ⟨q, hq⟩ :=
    (Polynomial.mem_map_range (algebraMap A K)).mpr hcoeff
  change q.map (algebraMap A K) = minpoly K z at hq
  have hqmonic : q.Monic := by
    apply ((IsFractionRing.injective A K).monic_map_iff).mpr
    rw [hq]
    exact minpoly.monic (Algebra.IsIntegral.isIntegral z)
  refine ⟨q, hqmonic, ?_⟩
  have hzmin := minpoly.aeval K z
  rw [← hq] at hzmin
  change Polynomial.aeval z q = 0
  simpa only [Polynomial.aeval_map_algebraMap] using hzmin

end EtaleFundamentalGroups
