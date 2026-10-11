/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.IntegralClosure.Localization.FractionFieldComparison
import EtaleFundamentalGroups.Purity.SpecialLocal.BaseMinimalPrime
import Mathlib.RingTheory.Etale.Field

/-!
# Generic etaleness of a finite separable normalization

The localization of an integral closure at its zero prime is its fraction
field.  Identifying that fraction field with the supplied finite separable
extension transports formal etaleness back to the literal localization used
by `Algebra.IsEtaleAt`.
-/

noncomputable section

namespace EtaleFundamentalGroups.SpecialLocalPurity

universe u v w

/-- The normalization in a finite separable extension is etale at its
generic point. -/
theorem integralClosure_isEtaleAt_bot_of_finite_separable
    {R : Type u} {K : Type v} {L : Type w}
    [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Algebra.IsEtaleAt R (⊥ : Ideal (integralClosure R L)) := by
  let C := integralClosure R L
  let q : Ideal C := ⊥
  let D := Localization.AtPrime q
  let : q.IsPrime := Ideal.isPrime_bot
  let : IsFractionRing C L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R K L C
  let : IsFractionRing C D := by
    simpa [D, q, Ideal.primeCompl_bot] using
      (Localization.isLocalization (M := q.primeCompl))
  let eC : D ≃ₐ[C] L :=
    IsLocalization.algEquiv (nonZeroDivisors C) D L
  let eR : D ≃ₐ[R] L := eC.restrictScalars R
  let : Algebra.FormallyEtale R K :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  let : Algebra.FormallyEtale K L :=
    Algebra.FormallyEtale.of_isSeparable K L
  let : Algebra.FormallyEtale R L :=
    Algebra.FormallyEtale.comp R K L
  exact Algebra.FormallyEtale.of_equiv eR.symm

/-- If a finite separable normalization is not formally etale but is etale
above every height-one base prime, its base cotangent support has a minimal
point of neither height zero nor height one. -/
theorem
    exists_minimal_integralClosure_base_nonEtaleCotangentSupport_codim_ge_two
    {R : Type u} {K : Type v} {L : Type w}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Finite R (integralClosure R L)]
    (hetale :
      ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
        ∀ (P : Ideal (integralClosure R L)) [P.IsPrime] [P.LiesOver p],
          Algebra.IsEtaleAt R P)
    (hne : ¬ Algebra.FormallyEtale R (integralClosure R L)) :
    ∃ p : PrimeSpectrum R,
      Minimal
        (· ∈ Module.support R Ω[(integralClosure R L)⁄R] ∪
          Module.support R
            (Algebra.H1Cotangent R (integralClosure R L))) p ∧
      p.asIdeal.height ≠ 0 ∧ p.asIdeal.height ≠ 1 := by
  obtain ⟨p, hp, P, hPp, hP⟩ :=
    exists_minimal_base_nonEtaleCotangentSupport_of_not_formallyEtale hne
  refine ⟨p, hp, ?_, ?_⟩
  · exact
      base_height_ne_zero_of_nonEtaleCotangentSupport_of_isEtaleAt_bot
        (integralClosure_isEtaleAt_bot_of_finite_separable
          (R := R) (K := K) (L := L)) p P hPp hP
  · exact
      base_height_ne_one_of_nonEtaleCotangentSupport_of_isEtaleAt_heightOne
        hetale p P hPp hP

/-- Numerical form of the preceding minimal-branch-point theorem: the bad
base point has height at least two. -/
theorem
    exists_minimal_integralClosure_base_nonEtaleCotangentSupport_height_two_le
    {R : Type u} {K : Type v} {L : Type w}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Finite R (integralClosure R L)]
    (hetale :
      ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
        ∀ (P : Ideal (integralClosure R L)) [P.IsPrime] [P.LiesOver p],
          Algebra.IsEtaleAt R P)
    (hne : ¬ Algebra.FormallyEtale R (integralClosure R L)) :
    ∃ p : PrimeSpectrum R,
      Minimal
        (· ∈ Module.support R Ω[(integralClosure R L)⁄R] ∪
          Module.support R
            (Algebra.H1Cotangent R (integralClosure R L))) p ∧
      (2 : ℕ∞) ≤ p.asIdeal.height := by
  obtain ⟨p, hp, hp0, hp1⟩ :=
    exists_minimal_integralClosure_base_nonEtaleCotangentSupport_codim_ge_two
      (R := R) (K := K) (L := L) hetale hne
  refine ⟨p, hp, ?_⟩
  by_contra htwo
  have hle : p.asIdeal.height ≤ 1 :=
    ENat.lt_two_iff.mp (lt_of_not_ge htwo)
  rcases Order.le_one_iff.mp hle with hzero | hone
  · exact hp0 hzero
  · exact hp1 hone

end EtaleFundamentalGroups.SpecialLocalPurity

end
