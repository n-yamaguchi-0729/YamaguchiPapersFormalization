/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.Local.RegularLocalCompletionDescent
import Nyll.EtaleFundamentalGroups.Purity.SpecialLocal.BaseMinimalPrimePuncturedPurity
import Nyll.EtaleFundamentalGroups.Purity.SpecialLocal.BaseMinimalPrime
import Nyll.EtaleFundamentalGroups.Purity.SpecialLocal.GenericPoint
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.Height
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Purity along a regular boundary

A hypothetical minimal non-étale point belongs to the specified boundary,
because the algebra is étale off that boundary. Generic and height-one
étaleness force its height to be at least two. Its regular local ring then
has punctured purity, contradicting the minimal non-étale point criterion.
Regularity is required only on the boundary, not on the whole base.
-/

noncomputable section

namespace EtaleFundamentalGroups.SpecialLocalPurity

universe u

/-- A finite normal-domain algebra is étale if it is generically étale,
étale in codimension one, and étale outside a boundary of regular points. -/
theorem finiteNormalDomainAlgebra_etale_of_regular_boundary
    {R S : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S))
    (Z : Set (PrimeSpectrum R))
    (hregular : ∀ p ∈ Z, IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (hgeneric : Algebra.IsEtaleAt R (⊥ : Ideal S))
    (haway : ∀ P : PrimeSpectrum S,
      PrimeSpectrum.comap (algebraMap R S) P ∉ Z → Algebra.IsEtaleAt R P.asIdeal)
    (hheightOne : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      ∀ (P : Ideal S) [P.IsPrime] [P.LiesOver p], Algebra.IsEtaleAt R P) :
    Algebra.Etale R S := by
  let : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hformally : Algebra.FormallyEtale R S := by
    by_contra hne
    obtain ⟨p, hp, P, hPp, hP⟩ :=
      exists_minimal_base_nonEtaleCotangentSupport_of_not_formallyEtale hne
    have hpZ : p ∈ Z := by
      by_contra hpZ
      have hPaway : PrimeSpectrum.comap (algebraMap R S) P ∉ Z := by
        rwa [hPp]
      have hLocus : P ∈ Algebra.etaleLocus R S := haway P hPaway
      rw [Algebra.etaleLocus_eq_compl_support] at hLocus
      exact hP.elim hLocus.1 hLocus.2
    have hp0 := base_height_ne_zero_of_nonEtaleCotangentSupport_of_isEtaleAt_bot
      hgeneric p P hPp hP
    have hp1 := base_height_ne_one_of_nonEtaleCotangentSupport_of_isEtaleAt_heightOne
      hheightOne p P hPp hP
    have hheight : (2 : ℕ∞) ≤ p.asIdeal.height := by
      by_contra htwo
      have hle : p.asIdeal.height ≤ 1 := ENat.lt_two_iff.mp (lt_of_not_ge htwo)
      rcases Order.le_one_iff.mp hle with hzero | hone
      · exact hp0 hzero
      · exact hp1 hone
    have hdim : (2 : WithBot ℕ∞) ≤
        ringKrullDim (Localization.AtPrime p.asIdeal) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
        (Localization.AtPrime p.asIdeal)]
      exact WithBot.coe_le_coe.mpr hheight
    let : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := hregular p hpZ
    exact not_minimal_base_nonEtaleCotangentSupport_of_hasPuncturedPurity hinj p hp
      (le_trans (by norm_num : (1 : WithBot ℕ∞) ≤ 2) hdim)
      (hasPuncturedPurity_of_isRegularLocalRing (Localization.AtPrime p.asIdeal) hdim)
  let : Algebra.FormallyEtale R S := hformally
  let : Module.FinitePresentation R S := Module.finitePresentation_of_finite R S
  let : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finitePresentation R S
  exact ⟨inferInstance, inferInstance⟩

/-- The normalization in a finite separable function-field extension is
étale when the branch locus is confined to regular boundary points and no
height-one ramification remains. Finiteness and generic étaleness of the
actual integral closure are supplied internally. -/
theorem integralClosure_etale_of_regular_boundary
    {R K L : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (Z : Set (PrimeSpectrum R))
    (hregular : ∀ p ∈ Z, IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (haway : ∀ P : PrimeSpectrum (integralClosure R L),
      PrimeSpectrum.comap (algebraMap R (integralClosure R L)) P ∉ Z →
        Algebra.IsEtaleAt R P.asIdeal)
    (hheightOne : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      ∀ (P : Ideal (integralClosure R L)) [P.IsPrime] [P.LiesOver p],
        Algebra.IsEtaleAt R P) :
    Algebra.Etale R (integralClosure R L) := by
  let : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R K L (integralClosure R L)
  let : IsIntegrallyClosed (integralClosure R L) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  have hinj : Function.Injective (algebraMap R (integralClosure R L)) := by
    intro x y hxy
    apply IsFractionRing.injective R K
    apply (algebraMap K L).injective
    rw [← IsScalarTower.algebraMap_apply R K L,
      ← IsScalarTower.algebraMap_apply R K L]
    exact congrArg (fun z : integralClosure R L ↦ (z : L)) hxy
  exact finiteNormalDomainAlgebra_etale_of_regular_boundary hinj Z hregular
    (integralClosure_isEtaleAt_bot_of_finite_separable (R := R) (K := K) (L := L))
    haway hheightOne

end EtaleFundamentalGroups.SpecialLocalPurity
