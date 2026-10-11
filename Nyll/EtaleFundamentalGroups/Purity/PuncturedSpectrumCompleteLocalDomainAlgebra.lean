/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumHypersurfaceDisconnectedReduction
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Direct algebra on the complete-local connectedness frontier

This file extracts the consequences of the two radical component ideals
produced by a disconnected punctured principal hypersurface.  In a domain,
the principal element is nonzero.  The component ideals also determine two
nonmaximal minimal primes over the principal ideal; Krull's principal ideal
theorem bounds both of their heights by one.
-/

noncomputable section

open IsLocalRing TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- In a local domain, a radical component decomposition of a principal
ideal into two nonmaximal pieces forces the principal element to be nonzero. -/
theorem ne_zero_of_radical_componentIntersection
    {C : Type u} [CommRing C] [IsDomain C] [IsLocalRing C]
    {x : C} {a b : Ideal C}
    (haRadical : a.IsRadical) (hbRadical : b.IsRadical)
    (haMax : a ≠ maximalIdeal C) (hbMax : b ≠ maximalIdeal C)
    (hinf : a ⊓ b = (Ideal.span {x}).radical)
    (hsup : (a ⊔ b).radical = maximalIdeal C) :
    x ≠ 0 := by
  have haBot : a ≠ ⊥ := by
    intro ha
    apply hbMax
    simpa only [ha, bot_inf_eq, bot_sup_eq, hbRadical.radical] using hsup
  have hbBot : b ≠ ⊥ := by
    intro hb
    apply haMax
    simpa only [hb, inf_bot_eq, sup_bot_eq, haRadical.radical] using hsup
  intro hx
  apply Ideal.inf_ne_bot_of_ne_bot haBot hbBot
  simpa only [hx, Set.singleton_zero, Ideal.span_zero,
    Ideal.radical_bot_of_isReduced] using hinf

/-- Two radical nonmaximal components whose intersection is `I.radical`
produce nonmaximal minimal primes over `I`, one containing each component.
Their sum still has maximal radical. -/
theorem exists_nonmaximal_minimalPrime_pair_of_radical_componentIntersection
    {C : Type u} [CommRing C] [IsLocalRing C]
    {I a b : Ideal C}
    (haRadical : a.IsRadical) (hbRadical : b.IsRadical)
    (haMax : a ≠ maximalIdeal C) (hbMax : b ≠ maximalIdeal C)
    (hinf : a ⊓ b = I.radical)
    (hsup : (a ⊔ b).radical = maximalIdeal C) :
    ∃ P Q : Ideal C,
      P ∈ I.minimalPrimes ∧ Q ∈ I.minimalPrimes ∧
      a ≤ P ∧ b ≤ Q ∧
      P ≠ maximalIdeal C ∧ Q ≠ maximalIdeal C ∧
      (P ⊔ Q).radical = maximalIdeal C := by
  have haTop : a ≠ ⊤ := by
    intro ha
    have hmaxTop : maximalIdeal C = ⊤ := by
      simpa only [ha, top_sup_eq, Ideal.radical_top] using hsup.symm
    exact (maximalIdeal.isMaximal C).ne_top hmaxTop
  have hbTop : b ≠ ⊤ := by
    intro hb
    have hmaxTop : maximalIdeal C = ⊤ := by
      simpa only [hb, sup_top_eq, Ideal.radical_top] using hsup.symm
    exact (maximalIdeal.isMaximal C).ne_top hmaxTop
  have haLt : a < maximalIdeal C :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal haTop) haMax
  have hbLt : b < maximalIdeal C :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hbTop) hbMax
  obtain ⟨ya, hyaMax, hya⟩ := (IsConcreteLE.lt_iff_le_and_exists.mp haLt).2
  obtain ⟨yb, hybMax, hyb⟩ := (IsConcreteLE.lt_iff_le_and_exists.mp hbLt).2
  have hPexists : ∃ P ∈ a.minimalPrimes, ya ∉ P := by
    by_contra h
    push Not at h
    have hyaInf : ya ∈ sInf a.minimalPrimes :=
      Ideal.mem_sInf.mpr fun P hP ↦ h P hP
    exact hya <| by
      simpa only [Ideal.sInf_minimalPrimes, haRadical.radical] using hyaInf
  have hQexists : ∃ Q ∈ b.minimalPrimes, yb ∉ Q := by
    by_contra h
    push Not at h
    have hybInf : yb ∈ sInf b.minimalPrimes :=
      Ideal.mem_sInf.mpr fun Q hQ ↦ h Q hQ
    exact hyb <| by
      simpa only [Ideal.sInf_minimalPrimes, hbRadical.radical] using hybInf
  obtain ⟨P, hPa, hyaP⟩ := hPexists
  obtain ⟨Q, hQb, hybQ⟩ := hQexists
  have hPMax : P ≠ maximalIdeal C := by
    intro hP
    exact hyaP (hP ▸ hyaMax)
  have hQMax : Q ≠ maximalIdeal C := by
    intro hQ
    exact hybQ (hQ ▸ hybMax)
  have hPI : P ∈ I.minimalPrimes := by
    refine ⟨⟨hPa.isPrime, ?_⟩, ?_⟩
    · exact Ideal.le_radical.trans <| hinf ▸ inf_le_left.trans hPa.le
    · intro p hp hpP
      have habp : a ⊓ b ≤ p := by
        rw [hinf]
        exact hp.1.radical_le_iff.mpr hp.2
      rcases hp.1.inf_le.mp habp with hap | hbp
      · exact hPa.2 ⟨hp.1, hap⟩ hpP
      · exfalso
        apply hPMax
        apply le_antisymm (IsLocalRing.le_maximalIdeal hPa.isPrime.ne_top)
        rw [← hsup]
        exact hPa.isPrime.isRadical.radical_le_iff.mpr <|
          sup_le hPa.le (hbp.trans hpP)
  have hQI : Q ∈ I.minimalPrimes := by
    refine ⟨⟨hQb.isPrime, ?_⟩, ?_⟩
    · exact Ideal.le_radical.trans <| hinf ▸ inf_le_right.trans hQb.le
    · intro q hq hqQ
      have habq : a ⊓ b ≤ q := by
        rw [hinf]
        exact hq.1.radical_le_iff.mpr hq.2
      rcases hq.1.inf_le.mp habq with haq | hbq
      · exfalso
        apply hQMax
        apply le_antisymm (IsLocalRing.le_maximalIdeal hQb.isPrime.ne_top)
        rw [← hsup]
        exact hQb.isPrime.isRadical.radical_le_iff.mpr <|
          sup_le (haq.trans hqQ) hQb.le
      · exact hQb.2 ⟨hq.1, hbq⟩ hqQ
  have hPQ : (P ⊔ Q).radical = maximalIdeal C := by
    apply le_antisymm
    · exact (maximalIdeal.isMaximal C).isPrime.isRadical.radical_le_iff.mpr <|
        sup_le (IsLocalRing.le_maximalIdeal hPa.isPrime.ne_top)
          (IsLocalRing.le_maximalIdeal hQb.isPrime.ne_top)
    · rw [← hsup]
      exact Ideal.radical_mono <| sup_le_sup hPa.le hQb.le
  exact ⟨P, Q, hPI, hQI, hPa.le, hQb.le, hPMax, hQMax, hPQ⟩

/-- For a principal intersection in a Noetherian local domain, the two
minimal primes supplied by the radical components both have height at most
one.  The principal element is simultaneously certified to be nonzero. -/
theorem exists_height_le_one_minimalPrime_pair_of_radical_componentIntersection
    {C : Type u} [CommRing C] [IsDomain C] [IsLocalRing C]
    [IsNoetherianRing C]
    {x : C} {a b : Ideal C}
    (haRadical : a.IsRadical) (hbRadical : b.IsRadical)
    (haMax : a ≠ maximalIdeal C) (hbMax : b ≠ maximalIdeal C)
    (hinf : a ⊓ b = (Ideal.span {x}).radical)
    (hsup : (a ⊔ b).radical = maximalIdeal C) :
    x ≠ 0 ∧
      ∃ P Q : Ideal C,
        P ∈ (Ideal.span {x}).minimalPrimes ∧
        Q ∈ (Ideal.span {x}).minimalPrimes ∧
        a ≤ P ∧ b ≤ Q ∧
        P ≠ maximalIdeal C ∧ Q ≠ maximalIdeal C ∧
        P.height ≤ 1 ∧ Q.height ≤ 1 ∧
        (P ⊔ Q).radical = maximalIdeal C := by
  refine ⟨ne_zero_of_radical_componentIntersection haRadical hbRadical
    haMax hbMax hinf hsup, ?_⟩
  obtain ⟨P, Q, hP, hQ, haP, hbQ, hPMax, hQMax, hPQ⟩ :=
    exists_nonmaximal_minimalPrime_pair_of_radical_componentIntersection
      haRadical hbRadical haMax hbMax hinf hsup
  exact ⟨P, Q, hP, hQ, haP, hbQ, hPMax, hQMax,
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hP,
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hQ, hPQ⟩

/-- A disconnected punctured principal hypersurface in a Noetherian local
domain supplies a nonzero equation and a pair of nonmaximal height-at-most-one
minimal primes whose sum has maximal radical. -/
theorem exists_height_le_one_minimalPrime_pair_of_not_connectedSpace
    {C : Type u} [CommRing C] [IsDomain C] [IsLocalRing C]
    [IsNoetherianRing C]
    (hdim : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C)
    (x : C) (hx : x ∈ maximalIdeal C) :
    letI : Nontrivial (C ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
          (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
    letI : IsLocalRing (C ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective
    ¬ ConnectedSpace (Scheme.puncturedSpectrum (C ⧸ Ideal.span {x})) →
      x ≠ 0 ∧
        ∃ P Q : Ideal C,
          P ∈ (Ideal.span {x}).minimalPrimes ∧
          Q ∈ (Ideal.span {x}).minimalPrimes ∧
          P ≠ maximalIdeal C ∧ Q ≠ maximalIdeal C ∧
          P.height ≤ 1 ∧ Q.height ≤ 1 ∧
          (P ⊔ Q).radical = maximalIdeal C := by
  let D := C ⧸ Ideal.span {x}
  let : Nontrivial D :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing D :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  intro hnot
  obtain ⟨a, b, _hxa, _hxb, _haTop, _hbTop, haMax, hbMax,
      haRadical, hbRadical, hinf, hsup⟩ :=
    exists_radical_nonmaximal_ambient_componentIntersectionIdeals_of_not_connectedSpace
      hdim x hx hnot
  obtain ⟨hx0, P, Q, hP, hQ, _haP, _hbQ, hPMax, hQMax,
      hPheight, hQheight, hPQ⟩ :=
    exists_height_le_one_minimalPrime_pair_of_radical_componentIntersection
      haRadical hbRadical haMax hbMax hinf hsup
  exact ⟨hx0, P, Q, hP, hQ, hPMax, hQMax, hPheight, hQheight, hPQ⟩

end AlgebraicGeometry.FiniteEtale

end
