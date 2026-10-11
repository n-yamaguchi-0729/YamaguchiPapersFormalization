/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.SpecialLocal.BaseMinimalPrimePuncturedPurity

/-!
# Generic etaleness supplies positive-dimensional minimal bad localizations

A minimal point of the base cotangent support of a finite domain algebra
cannot have height zero when the algebra is etale at its generic point.
Consequently its prime localization has positive Krull dimension.  This
removes the numerical hypothesis from the minimal-bad-point purity argument.
-/

noncomputable section

namespace EtaleFundamentalGroups.SpecialLocalPurity

universe u

/-- A prime of nonzero height has positive-dimensional prime localization. -/
theorem one_le_ringKrullDim_localizationAtPrime_of_height_ne_zero
    {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) (hp : p.asIdeal.height ≠ 0) :
    (1 : WithBot ℕ∞) ≤
      ringKrullDim (Localization.AtPrime p.asIdeal) := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
    p.asIdeal (Localization.AtPrime p.asIdeal)]
  rw [← WithBot.coe_one, WithBot.coe_le_coe]
  exact Order.one_le_iff_ne_zero.mpr hp

/-- Generic etaleness excludes height zero for every minimal point of the
base cotangent support of a finite domain algebra. -/
theorem
    minimal_base_nonEtaleCotangentSupport_height_ne_zero_of_isEtaleAt_bot
    {R S : Type u}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S]
    (hgeneric : Algebra.IsEtaleAt R (⊥ : Ideal S))
    (p : PrimeSpectrum R)
    (hp : Minimal
      (· ∈ Module.support R Ω[S⁄R] ∪
        Module.support R (Algebra.H1Cotangent R S)) p) :
    p.asIdeal.height ≠ 0 := by
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  let : Module.Finite S Ω[S⁄R] :=
    kaehlerDifferential_finite_of_finite_over_noetherian
  let : Module.Finite S (Algebra.H1Cotangent R S) :=
    h1Cotangent_finite_of_finite_over_noetherian
  let : Module.Finite R Ω[S⁄R] :=
    Module.Finite.trans (R := R) S Ω[S⁄R]
  let : Module.Finite R (Algebra.H1Cotangent R S) :=
    Module.Finite.trans (R := R) S (Algebra.H1Cotangent R S)
  rcases hp.1 with hpΩ | hpH1
  · rw [← image_comap_support_eq_support_of_finite
      (R := R) (S := S) (M := Ω[S⁄R])] at hpΩ
    obtain ⟨P, hP, hPp⟩ := hpΩ
    exact
      base_height_ne_zero_of_nonEtaleCotangentSupport_of_isEtaleAt_bot
        hgeneric p P hPp (Or.inl hP)
  · rw [← image_comap_support_eq_support_of_finite
      (R := R) (S := S) (M := Algebra.H1Cotangent R S)] at hpH1
    obtain ⟨P, hP, hPp⟩ := hpH1
    exact
      base_height_ne_zero_of_nonEtaleCotangentSupport_of_isEtaleAt_bot
        hgeneric p P hPp (Or.inr hP)

/-- Etaleness over every height-one base prime excludes height one for every
minimal point of the base cotangent support. -/
theorem
    minimal_base_nonEtaleCotangentSupport_height_ne_one_of_isEtaleAt_heightOne
    {R S : Type u}
    [CommRing R] [IsNoetherianRing R]
    [CommRing S]
    [Algebra R S] [Module.Finite R S]
    (hetale :
      ∀ (q : Ideal R) [q.IsPrime], q.height = 1 →
        ∀ (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q],
          Algebra.IsEtaleAt R Q)
    (p : PrimeSpectrum R)
    (hp : Minimal
      (· ∈ Module.support R Ω[S⁄R] ∪
        Module.support R (Algebra.H1Cotangent R S)) p) :
    p.asIdeal.height ≠ 1 := by
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let : Module.Finite S Ω[S⁄R] :=
    kaehlerDifferential_finite_of_finite_over_noetherian
  let : Module.Finite S (Algebra.H1Cotangent R S) :=
    h1Cotangent_finite_of_finite_over_noetherian
  let : Module.Finite R Ω[S⁄R] :=
    Module.Finite.trans (R := R) S Ω[S⁄R]
  let : Module.Finite R (Algebra.H1Cotangent R S) :=
    Module.Finite.trans (R := R) S (Algebra.H1Cotangent R S)
  rcases hp.1 with hpΩ | hpH1
  · rw [← image_comap_support_eq_support_of_finite
      (R := R) (S := S) (M := Ω[S⁄R])] at hpΩ
    obtain ⟨P, hP, hPp⟩ := hpΩ
    exact
      base_height_ne_one_of_nonEtaleCotangentSupport_of_isEtaleAt_heightOne
        hetale p P hPp (Or.inl hP)
  · rw [← image_comap_support_eq_support_of_finite
      (R := R) (S := S) (M := Algebra.H1Cotangent R S)] at hpH1
    obtain ⟨P, hP, hPp⟩ := hpH1
    exact
      base_height_ne_one_of_nonEtaleCotangentSupport_of_isEtaleAt_heightOne
        hetale p P hPp (Or.inr hP)

/-- At a minimal bad base point of a generically etale finite domain
algebra, the local base has positive Krull dimension. -/
theorem
one_le_ringKrullDim_localizationAtPrime_of_minimal_base_nonEtaleCotangentSupport_of_isEtaleAt_bot
    {R S : Type u}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S]
    (hgeneric : Algebra.IsEtaleAt R (⊥ : Ideal S))
    (p : PrimeSpectrum R)
    (hp : Minimal
      (· ∈ Module.support R Ω[S⁄R] ∪
        Module.support R (Algebra.H1Cotangent R S)) p) :
    (1 : WithBot ℕ∞) ≤
      ringKrullDim (Localization.AtPrime p.asIdeal) :=
  one_le_ringKrullDim_localizationAtPrime_of_height_ne_zero p
    (minimal_base_nonEtaleCotangentSupport_height_ne_zero_of_isEtaleAt_bot
      hgeneric p hp)

/-- A generically etale finite normal-domain algebra is formally etale when
the localizations at all hypothetical minimal bad base points have punctured
purity. -/
theorem
    finiteNormalDomainAlgebra_formallyEtale_of_genericEtale_of_minimalBadPuncturedPurity
    {R S : Type u}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S))
    (hgeneric : Algebra.IsEtaleAt R (⊥ : Ideal S))
    (hpurity : ∀ (p : PrimeSpectrum R),
      Minimal
        (· ∈ Module.support R Ω[S⁄R] ∪
          Module.support R (Algebra.H1Cotangent R S)) p →
      AlgebraicGeometry.FiniteEtale.HasPuncturedPurity
        (Localization.AtPrime p.asIdeal)) :
    Algebra.FormallyEtale R S :=
  finiteNormalDomainAlgebra_formallyEtale_of_minimalBadPuncturedPurity
    hinj
    (fun p hp ↦
      (
one_le_ringKrullDim_localizationAtPrime_of_minimal_base_nonEtaleCotangentSupport_of_isEtaleAt_bot
        hgeneric p hp))
    hpurity

/-- The finite-presentation consequence: under the preceding hypotheses the
original finite normal-domain algebra is etale. -/
theorem
    finiteNormalDomainAlgebra_etale_of_genericEtale_of_minimalBadPuncturedPurity
    {R S : Type u}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S))
    (hgeneric : Algebra.IsEtaleAt R (⊥ : Ideal S))
    (hpurity : ∀ (p : PrimeSpectrum R),
      Minimal
        (· ∈ Module.support R Ω[S⁄R] ∪
          Module.support R (Algebra.H1Cotangent R S)) p →
      AlgebraicGeometry.FiniteEtale.HasPuncturedPurity
        (Localization.AtPrime p.asIdeal)) :
    Algebra.Etale R S :=
  finiteNormalDomainAlgebra_etale_of_hasPuncturedPurity_at_minimal_base_nonEtaleCotangentSupport
    hinj
    (fun p hp ↦
      (
one_le_ringKrullDim_localizationAtPrime_of_minimal_base_nonEtaleCotangentSupport_of_isEtaleAt_bot
        hgeneric p hp))
    hpurity

/-- In the geometric codimension-two form, punctured purity is needed only
at minimal bad points which are not of height one.  Generic etaleness
supplies positive local dimension, while the height-one etaleness hypothesis
shows that every hypothetical minimal bad point satisfies this restriction. -/
theorem
    finiteNormalDomainAlgebra_formallyEtale_of_genericAndHeightOneEtale_of_minimalBadPurity
    {R S : Type u}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S))
    (hgeneric : Algebra.IsEtaleAt R (⊥ : Ideal S))
    (hetale :
      ∀ (q : Ideal R) [q.IsPrime], q.height = 1 →
        ∀ (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q],
          Algebra.IsEtaleAt R Q)
    (hpurity : ∀ (p : PrimeSpectrum R),
      (hp : Minimal
        (· ∈ Module.support R Ω[S⁄R] ∪
          Module.support R (Algebra.H1Cotangent R S)) p) →
      p.asIdeal.height ≠ 1 →
      AlgebraicGeometry.FiniteEtale.HasPuncturedPurity
        (Localization.AtPrime p.asIdeal)) :
    Algebra.FormallyEtale R S :=
  finiteNormalDomainAlgebra_formallyEtale_of_minimalBadPuncturedPurity
    hinj
    (fun p hp ↦
      (
one_le_ringKrullDim_localizationAtPrime_of_minimal_base_nonEtaleCotangentSupport_of_isEtaleAt_bot
        hgeneric p hp))
    (fun p hp ↦ hpurity p hp
      (minimal_base_nonEtaleCotangentSupport_height_ne_one_of_isEtaleAt_heightOne
        hetale p hp))

/-- Finite presentation upgrades the preceding codimension-two purity
criterion to global etaleness. -/
theorem
    finiteNormalDomainAlgebra_etale_of_genericAndHeightOneEtale_of_minimalBadPurity
    {R S : Type u}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S))
    (hgeneric : Algebra.IsEtaleAt R (⊥ : Ideal S))
    (hetale :
      ∀ (q : Ideal R) [q.IsPrime], q.height = 1 →
        ∀ (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q],
          Algebra.IsEtaleAt R Q)
    (hpurity : ∀ (p : PrimeSpectrum R),
      (hp : Minimal
        (· ∈ Module.support R Ω[S⁄R] ∪
          Module.support R (Algebra.H1Cotangent R S)) p) →
      p.asIdeal.height ≠ 1 →
      AlgebraicGeometry.FiniteEtale.HasPuncturedPurity
        (Localization.AtPrime p.asIdeal)) :
    Algebra.Etale R S := by
  let : Algebra.FormallyEtale R S :=
    finiteNormalDomainAlgebra_formallyEtale_of_genericAndHeightOneEtale_of_minimalBadPurity
      hinj hgeneric hetale hpurity
  let : Module.FinitePresentation R S :=
    Module.finitePresentation_of_finite R S
  let : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_finitePresentation R S
  exact ⟨inferInstance, inferInstance⟩

end EtaleFundamentalGroups.SpecialLocalPurity

end
