/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.LocalGeometry.HeightTwo.RegularPair
import EtaleFundamentalGroups.LocalGeometry.RegularLocal.DimensionTwoIntegrallyClosed
import EtaleFundamentalGroups.Purity.SpecialLocal.DimensionTwo.Core
import EtaleFundamentalGroups.Purity.SpecialLocal.DimensionTwoIntegralClosure

/-!
# Finite normalizations over a height-two regular local base

The regular-pair freeness theorem can be made input-free in dimension two.
A basis of the cotangent space lifts to a regular pair generating the maximal
ideal; trace-dual saturation then transports that pair to the finite
normalization.  Thus a finite normalization in a finite separable extension
is free, and hence flat, over the base.
-/

noncomputable section

namespace EtaleFundamentalGroups.SpecialLocalPurity

open IsLocalRing

universe u v w

/-- A normalization in a finite separable extension of the fraction field of
a two-dimensional regular local domain is finite.  Normality of the base is
produced from regularity and dimension two; finiteness then follows from the
trace-dual theorem for separable extensions. -/
theorem integralClosure_finite_of_isRegularLocalRing_dimension_two
    {A : Type u} {K : Type v} {L : Type w}
    [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hdim : ringKrullDim A = ((2 : ℕ∞) : WithBot ℕ∞)) :
    Module.Finite A (integralClosure A L) := by
  let : IsIntegrallyClosed A :=
    isIntegrallyClosed_of_isRegularLocalRing_dimension_two hdim
  exact IsIntegralClosure.finite A K L (integralClosure A L)

/-- A finite normalization over a two-dimensional regular local domain is
free.  The parameter pair is produced internally from the cotangent space. -/
theorem integralClosure_free_of_isRegularLocalRing_dimension_two
    {A : Type u} {K : Type v} {L : Type w}
    [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hdim : ringKrullDim A = ((2 : ℕ∞) : WithBot ℕ∞)) :
    Module.Free A (integralClosure A L) := by
  let : Module.Finite A (integralClosure A L) :=
    integralClosure_finite_of_isRegularLocalRing_dimension_two
      (K := K) hdim
  have hfin :
      Module.finrank (ResidueField A) (CotangentSpace A) = 2 := by
    have hreg :=
      (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance
    rw [hdim] at hreg
    exact ENat.natCast_inj.mp (WithBot.coe_eq_coe.mp hreg)
  obtain ⟨x, y, hregular, hspan⟩ :=
    EtaleFundamentalGroups.exists_regular_pair_of_finrank_cotangentSpace_eq_two_unconstrained
      hfin hdim
  exact integralClosure_free_of_regular_pair (K := K) hregular hspan

/-- A finite normalization over a two-dimensional regular local domain is
flat. -/
theorem integralClosure_flat_of_isRegularLocalRing_dimension_two
    {A : Type u} {K : Type v} {L : Type w}
    [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hdim : ringKrullDim A = ((2 : ℕ∞) : WithBot ℕ∞)) :
    Module.Flat A (integralClosure A L) := by
  let : Module.Free A (integralClosure A L) :=
    integralClosure_free_of_isRegularLocalRing_dimension_two
      (K := K) hdim
  infer_instance

/-- At a height-two prime of a regular domain, every normalization in a
finite separable extension of the local fraction field is finite. -/
theorem integralClosure_finite_localizationAtPrime_of_height_eq_two
    {A : Type u} [CommRing A] [IsDomain A] [IsRegularRing A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    {K : Type v} {L : Type w}
    [Field K] [Algebra (Localization.AtPrime P) K]
    [IsFractionRing (Localization.AtPrime P) K]
    [Field L] [Algebra (Localization.AtPrime P) L] [Algebra K L]
    [IsScalarTower (Localization.AtPrime P) K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Module.Finite (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L) := by
  have hdim :
      ringKrullDim (Localization.AtPrime P) =
        ((2 : ℕ∞) : WithBot ℕ∞) := by
    calc
      ringKrullDim (Localization.AtPrime P) =
          (P.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height
          P (Localization.AtPrime P)
      _ = ((2 : ℕ∞) : WithBot ℕ∞) :=
        congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hP
  exact integralClosure_finite_of_isRegularLocalRing_dimension_two
    (K := K) hdim

/-- At a height-two prime of a regular domain, every finite normalization in
a finite separable extension of the local fraction field is free. -/
theorem integralClosure_free_localizationAtPrime_of_height_eq_two
    {A : Type u} [CommRing A] [IsDomain A] [IsRegularRing A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    {K : Type v} {L : Type w}
    [Field K] [Algebra (Localization.AtPrime P) K]
    [IsFractionRing (Localization.AtPrime P) K]
    [Field L] [Algebra (Localization.AtPrime P) L] [Algebra K L]
    [IsScalarTower (Localization.AtPrime P) K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Module.Free (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L) := by
  have hdim :
      ringKrullDim (Localization.AtPrime P) =
        ((2 : ℕ∞) : WithBot ℕ∞) := by
    calc
      ringKrullDim (Localization.AtPrime P) =
          (P.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height
          P (Localization.AtPrime P)
      _ = ((2 : ℕ∞) : WithBot ℕ∞) :=
        congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hP
  exact integralClosure_free_of_isRegularLocalRing_dimension_two
    (K := K) hdim

/-- The finite normalization in the preceding height-two localization theorem
is flat. -/
theorem integralClosure_flat_localizationAtPrime_of_height_eq_two
    {A : Type u} [CommRing A] [IsDomain A] [IsRegularRing A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    {K : Type v} {L : Type w}
    [Field K] [Algebra (Localization.AtPrime P) K]
    [IsFractionRing (Localization.AtPrime P) K]
    [Field L] [Algebra (Localization.AtPrime P) L] [Algebra K L]
    [IsScalarTower (Localization.AtPrime P) K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Module.Flat (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L) := by
  let : Module.Free (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L) :=
    integralClosure_free_localizationAtPrime_of_height_eq_two
      P hP (K := K)
  infer_instance

/-- Purity endpoint for a finite normalization at a height-two point: if the
normalization is etale after localization at every height-one prime of the
local base, then it is already etale over the height-two local base.

Freeness and the regular parameter pair are both produced internally. -/
theorem integralClosure_etale_localizationAtPrime_of_height_eq_two
    {A : Type u} [CommRing A] [IsDomain A] [IsRegularRing A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    {K : Type v} {L : Type w}
    [Field K] [Algebra (Localization.AtPrime P) K]
    [IsFractionRing (Localization.AtPrime P) K]
    [Field L] [Algebra (Localization.AtPrime P) L] [Algebra K L]
    [IsScalarTower (Localization.AtPrime P) K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hlocal : ∀ (q : Ideal (Localization.AtPrime P)) [q.IsPrime],
      q.height = 1 →
      Algebra.Etale (Localization.AtPrime q)
        (Localization (Algebra.algebraMapSubmonoid
          (integralClosure (Localization.AtPrime P) L) q.primeCompl))) :
    Algebra.Etale (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L) := by
  let : Module.Finite (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L) :=
    integralClosure_finite_localizationAtPrime_of_height_eq_two
      P hP (K := K)
  let : Module.Free (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L) :=
    integralClosure_free_localizationAtPrime_of_height_eq_two
      P hP (K := K)
  obtain ⟨x, y, hregular, hspan⟩ :=
    EtaleFundamentalGroups.exists_regular_pair_localizationAtPrime_of_height_eq_two_unconstrained
      P hP
  exact etale_of_regular_pair_of_etale_localizationAtPrime
    hregular hspan hlocal

end EtaleFundamentalGroups.SpecialLocalPurity
