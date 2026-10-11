/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.SpecialLocal.AssociatedPrime

/-!
# Minimal non-etale points on the base

For a finite algebra, the image of each target cotangent support is its
support after restriction of scalars to the base.  Hence a non-etale algebra
has a minimal bad point on the base which is the contraction of an actual bad
point upstairs.  Every target prime contracting strictly below that base
point is etale.  This is the local input needed before applying punctured
purity at a minimal branch point.
-/

noncomputable section

namespace EtaleFundamentalGroups.SpecialLocalPurity

universe u v

/-- A non-formally-etale finite algebra has a minimal bad point on the base,
and that point is the contraction of an actual bad point upstairs. -/
theorem exists_minimal_base_nonEtaleCotangentSupport_of_not_formallyEtale
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [Algebra R S] [Module.Finite R S]
    (hne : ¬ Algebra.FormallyEtale R S) :
    ∃ p : PrimeSpectrum R,
      Minimal
        (· ∈ Module.support R Ω[S⁄R] ∪
          Module.support R (Algebra.H1Cotangent R S)) p ∧
      ∃ P : PrimeSpectrum S,
        PrimeSpectrum.comap (algebraMap R S) P = p ∧
        P ∈ Module.support S Ω[S⁄R] ∪
          Module.support S (Algebra.H1Cotangent R S) := by
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let : Module.Finite S Ω[S⁄R] :=
    kaehlerDifferential_finite_of_finite_over_noetherian
  let : Module.Finite S (Algebra.H1Cotangent R S) :=
    h1Cotangent_finite_of_finite_over_noetherian
  let : Module.Finite R Ω[S⁄R] :=
    Module.Finite.trans (R := R) S Ω[S⁄R]
  let : Module.Finite R (Algebra.H1Cotangent R S) :=
    Module.Finite.trans (R := R) S (Algebra.H1Cotangent R S)
  let T :=
    Module.support R Ω[S⁄R] ∪
      Module.support R (Algebra.H1Cotangent R S)
  obtain ⟨P₀, hP₀⟩ :=
    exists_minimal_nonEtaleCotangentSupport_of_not_formallyEtale hne
  have hp₀ : PrimeSpectrum.comap (algebraMap R S) P₀ ∈ T := by
    rcases hP₀.1 with hΩ | hH1
    · exact Or.inl (Module.support_subset_preimage_comap
        (R := R) (A := S) (M := Ω[S⁄R]) hΩ)
    · exact Or.inr (Module.support_subset_preimage_comap
        (R := R) (A := S) (M := Algebra.H1Cotangent R S) hH1)
  let IΩ := Module.annihilator R Ω[S⁄R]
  let IH1 := Module.annihilator R (Algebra.H1Cotangent R S)
  let J : Ideal R := IΩ ⊓ IH1
  have hJle : J ≤ (PrimeSpectrum.comap (algebraMap R S) P₀).asIdeal := by
    rcases hp₀ with hp₀ | hp₀
    · exact inf_le_left.trans (Module.mem_support_iff_of_finite.mp hp₀)
    · exact inf_le_right.trans (Module.mem_support_iff_of_finite.mp hp₀)
  have hJne : J ≠ ⊤ :=
    ne_top_of_le_ne_top
      (PrimeSpectrum.comap (algebraMap R S) P₀).isPrime.ne_top hJle
  obtain ⟨q, hq⟩ := J.nonempty_minimalPrimes hJne
  let p : PrimeSpectrum R := ⟨q, hq.isPrime⟩
  have hIq : IΩ ≤ q ∨ IH1 ≤ q := by
    apply hq.isPrime.inf_le.mp
    simpa only [J] using hq.le
  have hpSupport : p ∈ T := by
    rcases hIq with hIq | hIq
    · exact Or.inl (Module.mem_support_iff_of_finite.mpr hIq)
    · exact Or.inr (Module.mem_support_iff_of_finite.mpr hIq)
  have hpMinimal : Minimal (· ∈ T) p := by
    refine ⟨hpSupport, ?_⟩
    intro q' hq'Support hq'p
    have hJq' : J ≤ q'.asIdeal := by
      rcases hq'Support with hq' | hq'
      · exact inf_le_left.trans (Module.mem_support_iff_of_finite.mp hq')
      · exact inf_le_right.trans (Module.mem_support_iff_of_finite.mp hq')
    exact hq.2 ⟨q'.isPrime, hJq'⟩ hq'p
  refine ⟨p, hpMinimal, ?_⟩
  rcases hpSupport with hpΩ | hpH1
  · rw [← image_comap_support_eq_support_of_finite
      (R := R) (S := S) (M := Ω[S⁄R])] at hpΩ
    obtain ⟨P, hPΩ, hPp⟩ := hpΩ
    exact ⟨P, hPp, Or.inl hPΩ⟩
  · rw [← image_comap_support_eq_support_of_finite
      (R := R) (S := S) (M := Algebra.H1Cotangent R S)] at hpH1
    obtain ⟨P, hPH1, hPp⟩ := hpH1
    exact ⟨P, hPp, Or.inr hPH1⟩

/-- Above a base prime strictly below a minimal bad base point, every target
prime is etale. -/
theorem isEtaleAt_of_comap_lt_minimal_base_nonEtaleCotangentSupport
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S]
    (p : PrimeSpectrum R)
    (hp : Minimal
      (· ∈ Module.support R Ω[S⁄R] ∪
        Module.support R (Algebra.H1Cotangent R S)) p)
    (P : PrimeSpectrum S)
    (hPp : PrimeSpectrum.comap (algebraMap R S) P < p) :
    Algebra.IsEtaleAt R P.asIdeal := by
  change P ∈ Algebra.etaleLocus R S
  rw [Algebra.etaleLocus_eq_compl_support]
  constructor
  · intro hP
    have hbase : PrimeSpectrum.comap (algebraMap R S) P ∈
        Module.support R Ω[S⁄R] ∪
          Module.support R (Algebra.H1Cotangent R S) :=
      Or.inl (Module.support_subset_preimage_comap
        (R := R) (A := S) (M := Ω[S⁄R]) hP)
    exact (not_le_of_gt hPp) (hp.2 hbase hPp.le)
  · intro hP
    have hbase : PrimeSpectrum.comap (algebraMap R S) P ∈
        Module.support R Ω[S⁄R] ∪
          Module.support R (Algebra.H1Cotangent R S) :=
      Or.inr (Module.support_subset_preimage_comap
        (R := R) (A := S) (M := Algebra.H1Cotangent R S) hP)
    exact (not_le_of_gt hPp) (hp.2 hbase hPp.le)

/-- The contraction of an actual non-etale cotangent-support point cannot
have height one when every target prime above a height-one base prime is
etale. -/
theorem
    base_height_ne_one_of_nonEtaleCotangentSupport_of_isEtaleAt_heightOne
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S]
    (hetale :
      ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
        ∀ (P : Ideal S) [P.IsPrime] [P.LiesOver p],
          Algebra.IsEtaleAt R P)
    (p : PrimeSpectrum R) (P : PrimeSpectrum S)
    (hPp : PrimeSpectrum.comap (algebraMap R S) P = p)
    (hP : P ∈ Module.support S Ω[S⁄R] ∪
      Module.support S (Algebra.H1Cotangent R S)) :
    p.asIdeal.height ≠ 1 := by
  intro hp
  let : P.asIdeal.LiesOver p.asIdeal := ⟨by
    simpa [Ideal.under_def] using
      (congrArg PrimeSpectrum.asIdeal hPp).symm⟩
  have hEtale : Algebra.IsEtaleAt R P.asIdeal :=
    hetale p.asIdeal hp P.asIdeal
  have hLocus : P ∈ Algebra.etaleLocus R S := hEtale
  rw [Algebra.etaleLocus_eq_compl_support] at hLocus
  exact hP.elim hLocus.1 hLocus.2

/-- If a finite algebra is non-etale but etale above every height-one base
prime, its base cotangent support has a minimal point away from height one. -/
theorem exists_minimal_base_nonEtaleCotangentSupport_height_ne_one
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [Algebra R S] [Module.Finite R S]
    (hetale :
      ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
        ∀ (P : Ideal S) [P.IsPrime] [P.LiesOver p],
          Algebra.IsEtaleAt R P)
    (hne : ¬ Algebra.FormallyEtale R S) :
    ∃ p : PrimeSpectrum R,
      Minimal
        (· ∈ Module.support R Ω[S⁄R] ∪
          Module.support R (Algebra.H1Cotangent R S)) p ∧
      p.asIdeal.height ≠ 1 := by
  obtain ⟨p, hp, P, hPp, hP⟩ :=
    exists_minimal_base_nonEtaleCotangentSupport_of_not_formallyEtale hne
  exact ⟨p, hp,
    base_height_ne_one_of_nonEtaleCotangentSupport_of_isEtaleAt_heightOne
      hetale p P hPp hP⟩

/-- The contraction of an actual non-etale cotangent-support point cannot
have height zero when the integral domain extension is generically etale. -/
theorem
    base_height_ne_zero_of_nonEtaleCotangentSupport_of_isEtaleAt_bot
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S]
    (hgeneric : Algebra.IsEtaleAt R (⊥ : Ideal S))
    (p : PrimeSpectrum R) (P : PrimeSpectrum S)
    (hPp : PrimeSpectrum.comap (algebraMap R S) P = p)
    (hP : P ∈ Module.support S Ω[S⁄R] ∪
      Module.support S (Algebra.H1Cotangent R S)) :
    p.asIdeal.height ≠ 0 := by
  intro hp
  have hpbot : p.asIdeal = ⊥ :=
    Ideal.height_eq_zero_iff_eq_bot.mp hp
  let : P.asIdeal.LiesOver (⊥ : Ideal R) := ⟨by
    simpa [Ideal.under_def, hpbot] using
      (congrArg PrimeSpectrum.asIdeal hPp).symm⟩
  have hPbot : P.asIdeal = ⊥ :=
    Ideal.eq_bot_of_liesOver_bot R P.asIdeal
  have hEtale : Algebra.IsEtaleAt R P.asIdeal := by
    simpa only [hPbot] using hgeneric
  have hLocus : P ∈ Algebra.etaleLocus R S := hEtale
  rw [Algebra.etaleLocus_eq_compl_support] at hLocus
  exact hP.elim hLocus.1 hLocus.2

end EtaleFundamentalGroups.SpecialLocalPurity

end
