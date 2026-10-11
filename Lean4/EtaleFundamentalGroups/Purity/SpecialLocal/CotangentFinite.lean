/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Prime.Module

/-!
# Finite cotangent modules for special local purity

For a module-finite algebra over a Noetherian ring, both relative Kähler
differentials and first cotangent homology are finite over the target.  The
second assertion does not require projectivity of the differential module:
the target is Noetherian, so the kernel in a finite presentation of the
cotangent complex is finite.

This supplies the finiteness needed to replace minimal points of either
cotangent support by associated primes.  No purity or support-vanishing
hypothesis is used.
-/

noncomputable section

namespace EtaleFundamentalGroups.SpecialLocalPurity

universe u v

/-- Under a finite algebra, the support after restriction of scalars is
exactly the image of the original support on prime spectra.  The reverse
inclusion uses that an integral map is closed on spectra. -/
theorem image_comap_support_eq_support_of_finite
    {R : Type u} {S : Type v} {M : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite R S] [Module.Finite S M] :
    PrimeSpectrum.comap (algebraMap R S) '' Module.support S M =
      Module.support R M := by
  let : Module.Finite R M := Module.Finite.trans (R := R) S M
  rw [Module.support_eq_zeroLocus, Module.support_eq_zeroLocus,
    ← Module.comap_annihilator (R₀ := R) (R := S) (M := M)]
  have hclosed : IsClosed
      (PrimeSpectrum.comap (algebraMap R S) ''
        PrimeSpectrum.zeroLocus (Module.annihilator S M)) :=
    PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap R S)
      (Algebra.IsIntegral.isIntegral (R := R) (A := S)) _
      (PrimeSpectrum.isClosed_zeroLocus _)
  calc
    PrimeSpectrum.comap (algebraMap R S) ''
        PrimeSpectrum.zeroLocus (Module.annihilator S M) =
        closure (PrimeSpectrum.comap (algebraMap R S) ''
          PrimeSpectrum.zeroLocus (Module.annihilator S M)) :=
      hclosed.closure_eq.symm
    _ = PrimeSpectrum.zeroLocus
        ((Module.annihilator S M).comap (algebraMap R S)) :=
      PrimeSpectrum.closure_image_comap_zeroLocus
        (algebraMap R S) (Module.annihilator S M)

/-- Relative Kähler differentials of a finite algebra over a Noetherian ring
are finite over the target. -/
theorem kaehlerDifferential_finite_of_finite_over_noetherian
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [Module.Finite R S] :
    Module.Finite S Ω[S⁄R] := by
  let : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  infer_instance

/-- First cotangent homology of a finite algebra over a Noetherian ring is
finite over the target.  No projectivity assumption on `Ω[S⁄R]` is needed. -/
theorem h1Cotangent_finite_of_finite_over_noetherian
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [Module.Finite R S] :
    Module.Finite S (Algebra.H1Cotangent R S) := by
  let : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let P := Algebra.Presentation.ofFinitePresentation R S
  let : Module.Finite S P.toExtension.Cotangent :=
    Algebra.Extension.Cotangent.finite P.fg_ker
  let : Module.Finite S P.toExtension.H1Cotangent :=
    Module.Finite.of_injective P.toExtension.h1Cotangentι
      P.toExtension.h1Cotangentι_injective
  exact Module.Finite.equiv P.equivH1Cotangent

/-- Minimal primes in the annihilators of the two cotangent modules are
associated primes once the algebra is finite over a Noetherian base. -/
theorem cotangent_minimalPrimes_subset_associatedPrimes_of_finite_over_noetherian
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [Module.Finite R S] :
    (Module.annihilator S Ω[S⁄R]).minimalPrimes ⊆
        associatedPrimes S Ω[S⁄R] ∧
      (Module.annihilator S (Algebra.H1Cotangent R S)).minimalPrimes ⊆
        associatedPrimes S (Algebra.H1Cotangent R S) := by
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let : Module.Finite S Ω[S⁄R] :=
    kaehlerDifferential_finite_of_finite_over_noetherian
  let : Module.Finite S (Algebra.H1Cotangent R S) :=
    h1Cotangent_finite_of_finite_over_noetherian
  exact
    ⟨Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes S Ω[S⁄R],
      Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes S
        (Algebra.H1Cotangent R S)⟩

end EtaleFundamentalGroups.SpecialLocalPurity

end
