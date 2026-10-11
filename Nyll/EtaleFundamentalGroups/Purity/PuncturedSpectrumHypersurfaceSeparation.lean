/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumHypersurfaceIntersectionReduction

/-!
# Separations of a punctured hypersurface

An open separation of the puncture of a principal hypersurface assigns every
irreducible component to exactly one side.  The resulting two finite,
nonempty families of minimal primes have all cross-component intersections
supported at the closed point.
-/

noncomputable section

open IsLocalRing TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- An open separation of a punctured principal hypersurface produces two
finite nonempty families of minimal primes covering all minimal primes, with
cross-component intersections supported at the closed point. -/
theorem exists_minimalPrime_partition_of_open_puncture_partition
    {C : Type u} [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    (hdim : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C)
    (x : C) (hx : x ∈ maximalIdeal C) :
    letI : Nontrivial (C ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
          (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
    letI : IsLocalRing (C ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective
    ∀ {A₀ B₀ : Set (PrimeSpectrum (C ⧸ Ideal.span {x}))},
      IsOpen A₀ → IsOpen B₀ →
      A₀ ∪ B₀ =
        ({closedPoint (C ⧸ Ideal.span {x})}ᶜ :
          Set (PrimeSpectrum (C ⧸ Ideal.span {x}))) →
      Disjoint A₀ B₀ → A₀.Nonempty → B₀.Nonempty →
      ∃ S T : Set (Ideal (C ⧸ Ideal.span {x})),
        S.Nonempty ∧ T.Nonempty ∧
        S.Finite ∧ T.Finite ∧
        S ∪ T = minimalPrimes (C ⧸ Ideal.span {x}) ∧
        Disjoint S T ∧
        ∀ P ∈ S, ∀ Q ∈ T,
          PrimeSpectrum.zeroLocus P ∩ PrimeSpectrum.zeroLocus Q ⊆
            ({closedPoint (C ⧸ Ideal.span {x})} :
              Set (PrimeSpectrum (C ⧸ Ideal.span {x}))) := by
  let D := C ⧸ Ideal.span {x}
  let : Nontrivial D :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing D :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  intro A₀ B₀ hAopen hBopen hcover hdisjoint hAnonempty hBnonempty
  let U : Set (PrimeSpectrum D) := {closedPoint D}ᶜ
  let S : Set (Ideal D) :=
    {P | P ∈ minimalPrimes D ∧ PrimeSpectrum.zeroLocus P ∩ U ⊆ A₀}
  let T : Set (Ideal D) :=
    {P | P ∈ minimalPrimes D ∧ PrimeSpectrum.zeroLocus P ∩ U ⊆ B₀}
  have hcomponent (P : Ideal D) (hP : P ∈ minimalPrimes D) :
      PrimeSpectrum.zeroLocus P ∈ irreducibleComponents (PrimeSpectrum D) := by
    rw [PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents]
    simpa only [(hP.isPrime.isRadical.radical)] using hP
  have hcomponentMeets (P : Ideal D) (hP : P ∈ minimalPrimes D) :
      (PrimeSpectrum.zeroLocus P ∩ U).Nonempty := by
    exact irreducibleComponent_quotient_span_singleton_inter_puncture_nonempty
      hdim x hx (PrimeSpectrum.zeroLocus P) (hcomponent P hP)
  have hside (P : Ideal D) (hP : P ∈ minimalPrimes D) : P ∈ S ∨ P ∈ T := by
    have hsides := irreducibleComponent_inter_subset_partition_side
      (PrimeSpectrum.zeroLocus P) (hcomponent P hP)
      hAopen hBopen hcover hdisjoint
    exact hsides.imp (fun h ↦ ⟨hP, h⟩) (fun h ↦ ⟨hP, h⟩)
  have hSnonempty : S.Nonempty := by
    obtain ⟨a, haA⟩ := hAnonempty
    have haU : a ∈ U := by
      change a ∈ ({closedPoint D}ᶜ : Set (PrimeSpectrum D))
      rw [← hcover]
      exact Or.inl haA
    obtain ⟨P, hP, hPa⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal D))
        (J := a.asIdeal) bot_le
    rcases hside P hP with hPS | hPT
    · exact ⟨P, hPS⟩
    · exfalso
      exact Set.disjoint_left.mp hdisjoint haA
        (hPT.2 ⟨hPa, haU⟩)
  have hTnonempty : T.Nonempty := by
    obtain ⟨b, hbB⟩ := hBnonempty
    have hbU : b ∈ U := by
      change b ∈ ({closedPoint D}ᶜ : Set (PrimeSpectrum D))
      rw [← hcover]
      exact Or.inr hbB
    obtain ⟨Q, hQ, hQb⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal D))
        (J := b.asIdeal) bot_le
    rcases hside Q hQ with hQS | hQT
    · exfalso
      exact Set.disjoint_left.mp hdisjoint
        (hQS.2 ⟨hQb, hbU⟩) hbB
    · exact ⟨Q, hQT⟩
  have hSfinite : S.Finite :=
    (minimalPrimes.finite_of_isNoetherianRing D).subset fun _ h ↦ h.1
  have hTfinite : T.Finite :=
    (minimalPrimes.finite_of_isNoetherianRing D).subset fun _ h ↦ h.1
  have hSTcover : S ∪ T = minimalPrimes D := by
    apply Set.Subset.antisymm
    · exact fun _ h ↦ h.elim (fun h ↦ h.1) (fun h ↦ h.1)
    · intro P hP
      exact hside P hP
  have hSTdisjoint : Disjoint S T := by
    rw [Set.disjoint_left]
    intro P hPS hPT
    obtain ⟨p, hpPU⟩ := hcomponentMeets P hPS.1
    exact Set.disjoint_left.mp hdisjoint
      (hPS.2 hpPU) (hPT.2 hpPU)
  refine ⟨S, T, hSnonempty, hTnonempty, hSfinite, hTfinite,
    hSTcover, hSTdisjoint, ?_⟩
  intro P hPS Q hQT p hp
  have hpNotU : p ∉ U := by
    intro hpU
    exact Set.disjoint_left.mp hdisjoint
      (hPS.2 ⟨hp.1, hpU⟩) (hQT.2 ⟨hp.2, hpU⟩)
  simpa only [U, Set.mem_compl_iff, Set.mem_singleton_iff, not_not]
    using hpNotU

/-- Ideal-theoretic output of an open separation: the intersections of the
two component families meet in the nilradical, while the radical of their
sum is the maximal ideal. -/
theorem exists_componentIntersectionIdeals_of_open_puncture_partition
    {C : Type u} [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    (hdim : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C)
    (x : C) (hx : x ∈ maximalIdeal C) :
    letI : Nontrivial (C ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
          (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
    letI : IsLocalRing (C ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective
    ∀ {A₀ B₀ : Set (PrimeSpectrum (C ⧸ Ideal.span {x}))},
      IsOpen A₀ → IsOpen B₀ →
      A₀ ∪ B₀ =
        ({closedPoint (C ⧸ Ideal.span {x})}ᶜ :
          Set (PrimeSpectrum (C ⧸ Ideal.span {x}))) →
      Disjoint A₀ B₀ → A₀.Nonempty → B₀.Nonempty →
      ∃ a b : Ideal (C ⧸ Ideal.span {x}),
        a ⊓ b = nilradical (C ⧸ Ideal.span {x}) ∧
        (a ⊔ b).radical = maximalIdeal (C ⧸ Ideal.span {x}) := by
  let D := C ⧸ Ideal.span {x}
  let : Nontrivial D :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing D :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  intro A₀ B₀ hAopen hBopen hcover hdisjoint hAnonempty hBnonempty
  obtain ⟨S, T, hSnonempty, hTnonempty, hSfinite, hTfinite,
      hSTcover, _hSTdisjoint, hcross⟩ :=
    exists_minimalPrime_partition_of_open_puncture_partition
      hdim x hx hAopen hBopen hcover hdisjoint hAnonempty hBnonempty
  have hSsub : S ⊆ (⊥ : Ideal D).minimalPrimes := by
    intro P hPS
    change P ∈ minimalPrimes D
    rw [← hSTcover]
    exact Or.inl hPS
  have hTsub : T ⊆ (⊥ : Ideal D).minimalPrimes := by
    intro Q hQT
    change Q ∈ minimalPrimes D
    rw [← hSTcover]
    exact Or.inr hQT
  have hradical : (sInf S ⊔ sInf T).radical = maximalIdeal D :=
    radical_sup_sInf_eq_maximalIdeal_of_minimalPrime_cross_zeroLocus
      (⊥ : Ideal D) hSsub hTsub hSnonempty hTnonempty hcross
  have hinf : sInf S ⊓ sInf T = nilradical D := by
    rw [← sInf_union, hSTcover, Ideal.sInf_minimalPrimes]
    rfl
  exact ⟨sInf S, sInf T, hinf, hradical⟩

/-- The two component-intersection ideals produced by a nontrivial open
separation are proper.  This is the form used by complete-local intersection
theorems: two proper closed subsets cover the hypersurface, while their
scheme-theoretic intersection is supported only at the closed point. -/
theorem exists_proper_componentIntersectionIdeals_of_open_puncture_partition
    {C : Type u} [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    (hdim : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C)
    (x : C) (hx : x ∈ maximalIdeal C) :
    letI : Nontrivial (C ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
          (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
    letI : IsLocalRing (C ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective
    ∀ {A₀ B₀ : Set (PrimeSpectrum (C ⧸ Ideal.span {x}))},
      IsOpen A₀ → IsOpen B₀ →
      A₀ ∪ B₀ =
        ({closedPoint (C ⧸ Ideal.span {x})}ᶜ :
          Set (PrimeSpectrum (C ⧸ Ideal.span {x}))) →
      Disjoint A₀ B₀ → A₀.Nonempty → B₀.Nonempty →
      ∃ a b : Ideal (C ⧸ Ideal.span {x}),
        a ≠ ⊤ ∧ b ≠ ⊤ ∧
        a ⊓ b = nilradical (C ⧸ Ideal.span {x}) ∧
        (a ⊔ b).radical = maximalIdeal (C ⧸ Ideal.span {x}) := by
  let D := C ⧸ Ideal.span {x}
  let : Nontrivial D :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing D :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  intro A₀ B₀ hAopen hBopen hcover hdisjoint hAnonempty hBnonempty
  obtain ⟨a, b, hinf, hradical⟩ :=
    exists_componentIntersectionIdeals_of_open_puncture_partition
      hdim x hx hAopen hBopen hcover hdisjoint hAnonempty hBnonempty
  have ha : a ≠ ⊤ := by
    intro ha
    rw [ha, sup_eq_left.mpr le_top, Ideal.radical_top] at hradical
    exact (maximalIdeal.isMaximal D).ne_top hradical.symm
  have hb : b ≠ ⊤ := by
    intro hb
    rw [hb, sup_eq_right.mpr le_top, Ideal.radical_top] at hradical
    exact (maximalIdeal.isMaximal D).ne_top hradical.symm
  exact ⟨a, b, ha, hb, hinf, hradical⟩

/-- The component-intersection construction records that its two ideals are
radical and nonmaximal.  This is source-produced information: each ideal is an
intersection of minimal primes and lies below a nonmaximal minimal prime
belonging to its side of the partition. -/
theorem exists_radical_nonmaximal_componentIntersectionIdeals_of_open_puncture_partition
    {C : Type u} [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    (hdim : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C)
    (x : C) (hx : x ∈ maximalIdeal C) :
    letI : Nontrivial (C ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
          (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
    letI : IsLocalRing (C ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective
    ∀ {A₀ B₀ : Set (PrimeSpectrum (C ⧸ Ideal.span {x}))},
      IsOpen A₀ → IsOpen B₀ →
      A₀ ∪ B₀ =
        ({closedPoint (C ⧸ Ideal.span {x})}ᶜ :
          Set (PrimeSpectrum (C ⧸ Ideal.span {x}))) →
      Disjoint A₀ B₀ → A₀.Nonempty → B₀.Nonempty →
      ∃ a b : Ideal (C ⧸ Ideal.span {x}),
        a ≠ ⊤ ∧ b ≠ ⊤ ∧
        a ≠ maximalIdeal (C ⧸ Ideal.span {x}) ∧
        b ≠ maximalIdeal (C ⧸ Ideal.span {x}) ∧
        a.IsRadical ∧ b.IsRadical ∧
        a ⊓ b = nilradical (C ⧸ Ideal.span {x}) ∧
        (a ⊔ b).radical = maximalIdeal (C ⧸ Ideal.span {x}) := by
  let D := C ⧸ Ideal.span {x}
  let : Nontrivial D :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing D :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  intro A₀ B₀ hAopen hBopen hcover hdisjoint hAnonempty hBnonempty
  obtain ⟨S, T, hSnonempty, hTnonempty, _hSfinite, _hTfinite,
      hSTcover, _hSTdisjoint, hcross⟩ :=
    exists_minimalPrime_partition_of_open_puncture_partition
      hdim x hx hAopen hBopen hcover hdisjoint hAnonempty hBnonempty
  have hSsub : S ⊆ (⊥ : Ideal D).minimalPrimes := by
    intro P hPS
    change P ∈ minimalPrimes D
    rw [← hSTcover]
    exact Or.inl hPS
  have hTsub : T ⊆ (⊥ : Ideal D).minimalPrimes := by
    intro Q hQT
    change Q ∈ minimalPrimes D
    rw [← hSTcover]
    exact Or.inr hQT
  have hradical : (sInf S ⊔ sInf T).radical = maximalIdeal D :=
    radical_sup_sInf_eq_maximalIdeal_of_minimalPrime_cross_zeroLocus
      (⊥ : Ideal D) hSsub hTsub hSnonempty hTnonempty hcross
  have hinf : sInf S ⊓ sInf T = nilradical D := by
    rw [← sInf_union, hSTcover, Ideal.sInf_minimalPrimes]
    rfl
  obtain ⟨P, hPS⟩ := hSnonempty
  obtain ⟨Q, hQT⟩ := hTnonempty
  have hPne : P ≠ maximalIdeal D :=
    minimalPrime_quotient_span_singleton_ne_maximalIdeal
      hdim x hx P (hSsub hPS)
  have hQne : Q ≠ maximalIdeal D :=
    minimalPrime_quotient_span_singleton_ne_maximalIdeal
      hdim x hx Q (hTsub hQT)
  have ha : sInf S ≠ ⊤ := by
    intro ha
    exact (hSsub hPS).isPrime.ne_top <| top_unique <| ha ▸ sInf_le hPS
  have hb : sInf T ≠ ⊤ := by
    intro hb
    exact (hTsub hQT).isPrime.ne_top <| top_unique <| hb ▸ sInf_le hQT
  have hamax : sInf S ≠ maximalIdeal D := by
    intro ha
    apply hPne
    exact le_antisymm (le_maximalIdeal (hSsub hPS).isPrime.ne_top)
      (ha ▸ sInf_le hPS)
  have hbmax : sInf T ≠ maximalIdeal D := by
    intro hb
    apply hQne
    exact le_antisymm (le_maximalIdeal (hTsub hQT).isPrime.ne_top)
      (hb ▸ sInf_le hQT)
  have haRadical : (sInf S).IsRadical := by
    rw [sInf_eq_iInf]
    apply Ideal.isRadical_iInf
    intro P
    apply Ideal.isRadical_iInf
    intro hPS
    exact (hSsub hPS).isPrime.isRadical
  have hbRadical : (sInf T).IsRadical := by
    rw [sInf_eq_iInf]
    apply Ideal.isRadical_iInf
    intro Q
    apply Ideal.isRadical_iInf
    intro hQT
    exact (hTsub hQT).isPrime.isRadical
  exact
    ⟨sInf S, sInf T, ha, hb, hamax, hbmax, haRadical, hbRadical,
      hinf, hradical⟩

/-- The component-intersection ideals are not the maximal ideal.  Thus both
closed component families still meet the puncture; this is stronger than
mere properness and is the exact nonemptiness input in the algebraic
connectedness criterion. -/
theorem exists_nonmaximal_componentIntersectionIdeals_of_open_puncture_partition
    {C : Type u} [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    (hdim : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C)
    (x : C) (hx : x ∈ maximalIdeal C) :
    letI : Nontrivial (C ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
          (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
    letI : IsLocalRing (C ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective
    ∀ {A₀ B₀ : Set (PrimeSpectrum (C ⧸ Ideal.span {x}))},
      IsOpen A₀ → IsOpen B₀ →
      A₀ ∪ B₀ =
        ({closedPoint (C ⧸ Ideal.span {x})}ᶜ :
          Set (PrimeSpectrum (C ⧸ Ideal.span {x}))) →
      Disjoint A₀ B₀ → A₀.Nonempty → B₀.Nonempty →
      ∃ a b : Ideal (C ⧸ Ideal.span {x}),
        a ≠ ⊤ ∧ b ≠ ⊤ ∧
        a ≠ maximalIdeal (C ⧸ Ideal.span {x}) ∧
        b ≠ maximalIdeal (C ⧸ Ideal.span {x}) ∧
        a ⊓ b = nilradical (C ⧸ Ideal.span {x}) ∧
        (a ⊔ b).radical = maximalIdeal (C ⧸ Ideal.span {x}) := by
  let D := C ⧸ Ideal.span {x}
  let : Nontrivial D :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing D :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  intro A₀ B₀ hAopen hBopen hcover hdisjoint hAnonempty hBnonempty
  obtain ⟨a, b, ha, hb, hamax, hbmax, _haRadical, _hbRadical,
      hinf, hradical⟩ :=
    exists_radical_nonmaximal_componentIntersectionIdeals_of_open_puncture_partition
      hdim x hx hAopen hBopen hcover hdisjoint hAnonempty hBnonempty
  exact ⟨a, b, ha, hb, hamax, hbmax, hinf, hradical⟩

end AlgebraicGeometry.FiniteEtale

end
