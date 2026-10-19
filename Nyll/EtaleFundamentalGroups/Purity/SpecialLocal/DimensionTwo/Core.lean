/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.Trace.FiniteFreeDiscriminant
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Smooth.Fiber

/-!
# Dimension-two purity for finite free algebras

For a finite free algebra, formal unramifiedness is detected by the trace
discriminant.  Over a Noetherian domain, a nonzero element whose image is a
unit at every height-one localization is already a unit: otherwise a minimal
prime over its principal ideal gives a height-one point where its image lies
in the maximal ideal.

A regular pair generating the maximal ideal supplies a height-one prime, so
the discriminant cannot vanish.  Consequently, if every height-one
localization of a finite free algebra is etale, its global discriminant is a
unit and the algebra is etale over the base.
-/

noncomputable section

namespace EtaleFundamentalGroups.SpecialLocalPurity

open IsLocalRing Module
open RingTheory.Sequence

universe u v

/-- A nonzero nonunit in a Noetherian domain is contained in a height-one
prime.  The prime is chosen minimal over the element's principal ideal. -/
theorem exists_height_one_prime_containing_of_nonzero_nonunit
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {d : A} (hd : d ≠ 0) (hdu : ¬ IsUnit d) :
    ∃ p : Ideal A, p.IsPrime ∧ p.height = 1 ∧ d ∈ p := by
  obtain ⟨p, hpMin⟩ :=
    (Ideal.span ({d} : Set A)).nonempty_minimalPrimes (by simpa)
  have hpNe : p ≠ ⊥ := by
    intro hp
    apply hd
    apply Ideal.span_singleton_eq_bot.mp
    exact bot_unique (hpMin.le.trans_eq hp)
  have hpHeight : p.height = 1 := by
    let : p.IsPrime := hpMin.isPrime
    apply le_antisymm
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
        (Ideal.span ({d} : Set A)) p hpMin
    · exact (Order.one_le_iff_ne_zero.mpr
        (Ideal.height_eq_zero_iff_eq_bot.not.mpr hpNe))
  exact ⟨p, hpMin.isPrime, hpHeight,
    hpMin.le (Ideal.mem_span_singleton_self d)⟩

/-- In a Noetherian domain, a nonzero element which becomes a unit at
every height-one localization is a unit. -/
theorem isUnit_of_isUnit_localizationAtPrime_height_one
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {d : A} (hd : d ≠ 0)
    (hlocal : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
      IsUnit (algebraMap A (Localization.AtPrime p) d)) :
    IsUnit d := by
  by_contra hdu
  obtain ⟨p, hpPrime, hpHeight, hdMem⟩ :=
    exists_height_one_prime_containing_of_nonzero_nonunit hd hdu
  let : p.IsPrime := hpPrime
  have hdUnit := hlocal p hpHeight
  have hdLocalMem : algebraMap A (Localization.AtPrime p) d ∈
      maximalIdeal (Localization.AtPrime p) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime p) p d).mpr hdMem
  have hdNotUnit : ¬ IsUnit (algebraMap A (Localization.AtPrime p) d) := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hdLocalMem
  exact hdNotUnit hdUnit

/-- A regular pair generating the maximal ideal of a Noetherian local
domain produces a height-one prime. -/
theorem exists_height_one_prime_of_regular_pair
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A]
    {x y : A} (hregular : IsRegular A [x, y])
    (hspan : Ideal.ofList [x, y] = maximalIdeal A) :
    ∃ p : Ideal A, p.IsPrime ∧ p.height = 1 := by
  have hxRegular : IsSMulRegular A x :=
    ((isRegular_cons_iff A x [y]).mp hregular).1
  have hx : x ≠ 0 := by
    intro hx
    exact one_ne_zero (hxRegular.right_eq_zero_of_smul (by simp [hx]))
  have hxMem : x ∈ maximalIdeal A := by
    rw [← hspan]
    exact Ideal.subset_span List.mem_cons_self
  have hxNotUnit : ¬ IsUnit x := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hxMem
  obtain ⟨p, hpPrime, hpHeight, -⟩ :=
    exists_height_one_prime_containing_of_nonzero_nonunit hx hxNotUnit
  exact ⟨p, hpPrime, hpHeight⟩

/-- A finite free algebra over a Noetherian domain is etale when a
height-one prime exists and every height-one localization is etale. -/
theorem etale_of_exists_height_one_prime_of_etale_localizationAtPrime
    {A : Type u} {S : Type v}
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing S] [Algebra A S] [Module.Free A S] [Module.Finite A S]
    (hexists : ∃ p : Ideal A, p.IsPrime ∧ p.height = 1)
    (hlocal : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
      Algebra.Etale (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))) :
    Algebra.Etale A S := by
  let ι := Module.Free.ChooseBasisIndex A S
  let : Fintype ι := Fintype.ofFinite ι
  let : DecidableEq ι := Classical.decEq ι
  let b : Basis ι A S := Module.Free.chooseBasis A S
  let d : A := Algebra.discr A b
  have hdiscrLocal : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
      IsUnit (algebraMap A (Localization.AtPrime p) d) := by
    intro p _ hpHeight
    let Aₚ := Localization.AtPrime p
    let Sₚ := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
    let : Algebra.Etale Aₚ Sₚ := hlocal p hpHeight
    let : Algebra.FormallyUnramified Aₚ Sₚ := inferInstance
    let bₚ : Basis ι Aₚ Sₚ :=
      b.localizationLocalization Aₚ p.primeCompl Sₚ
    have hunit : IsUnit (Algebra.discr Aₚ bₚ) :=
      (EtaleFundamentalGroups.formallyUnramified_iff_isUnit_discr bₚ).mp inferInstance
    rw [Algebra.discr_localizationLocalization A p.primeCompl Sₚ b] at hunit
    exact hunit
  obtain ⟨p, hpPrime, hpHeight⟩ := hexists
  let : p.IsPrime := hpPrime
  have hd : d ≠ 0 := by
    intro hd
    have hunit := hdiscrLocal p hpHeight
    rw [hd, map_zero] at hunit
    exact not_isUnit_zero hunit
  have hunit : IsUnit d :=
    isUnit_of_isUnit_localizationAtPrime_height_one hd hdiscrLocal
  let : Algebra.FormallyUnramified A S :=
    (EtaleFundamentalGroups.formallyUnramified_iff_isUnit_discr b).mpr hunit
  let : Module.FinitePresentation A S :=
    Module.finitePresentation_of_projective A S
  let : Algebra.FinitePresentation A S := inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- Dimension-two special local purity in regular-parameter form: if a
regular pair generates the maximal ideal, a finite free algebra which is
etale after localization at every height-one prime is globally etale. -/
theorem etale_of_regular_pair_of_etale_localizationAtPrime
    {A : Type u} {S : Type v}
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A]
    [CommRing S] [Algebra A S] [Module.Free A S] [Module.Finite A S]
    {x y : A} (hregular : IsRegular A [x, y])
    (hspan : Ideal.ofList [x, y] = maximalIdeal A)
    (hlocal : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
      Algebra.Etale (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))) :
    Algebra.Etale A S := by
  apply etale_of_exists_height_one_prime_of_etale_localizationAtPrime
    (exists_height_one_prime_of_regular_pair hregular hspan)
  exact hlocal

end EtaleFundamentalGroups.SpecialLocalPurity

end
