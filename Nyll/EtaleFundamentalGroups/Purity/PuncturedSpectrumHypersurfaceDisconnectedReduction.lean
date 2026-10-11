/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumHypersurfaceAmbientIdeals

/-!
# Algebraic data from a disconnected punctured hypersurface

Disconnectedness of the punctured spectrum gives an honest clopen
separation.  Because the puncture is itself an ambient open subset, both
sides lift to ambient open sets.  The component reduction then produces the
two proper ideals required by the complete-local intersection theorem.
-/

noncomputable section

open IsLocalRing TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- A disconnected punctured hypersurface produces ambient component ideals
that are radical and nonmaximal. -/
theorem exists_radical_nonmaximal_ambient_componentIntersectionIdeals_of_not_connectedSpace
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
    ¬ ConnectedSpace
        (Scheme.puncturedSpectrum (C ⧸ Ideal.span {x})) →
      ∃ a b : Ideal C,
        Ideal.span {x} ≤ a ∧ Ideal.span {x} ≤ b ∧
        a ≠ ⊤ ∧ b ≠ ⊤ ∧
        a ≠ maximalIdeal C ∧ b ≠ maximalIdeal C ∧
        a.IsRadical ∧ b.IsRadical ∧
        a ⊓ b = (Ideal.span {x}).radical ∧
        (a ⊔ b).radical = maximalIdeal C := by
  let D := C ⧸ Ideal.span {x}
  let : Nontrivial D :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing D :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  intro hnot
  let U := Scheme.puncturedSpectrumOpen D
  have hU_nonempty : Nonempty U := by
    obtain ⟨P, hP, _⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal D))
        (J := maximalIdeal D) bot_le
    have hcomponent :
        PrimeSpectrum.zeroLocus P ∈
          irreducibleComponents (PrimeSpectrum D) := by
      rw [PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents]
      simpa only [(hP.isPrime.isRadical.radical)] using hP
    obtain ⟨p, _hpComponent, hpPuncture⟩ :=
      irreducibleComponent_quotient_span_singleton_inter_puncture_nonempty
        hdim x hx (PrimeSpectrum.zeroLocus P) hcomponent
    refine ⟨⟨p, ?_⟩⟩
    exact (Scheme.mem_puncturedSpectrumOpen_iff D p).2 <| by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]
        using hpPuncture
  have hnontrivialClopen :
      ∃ A : Set U, IsClopen A ∧ A ≠ ∅ ∧ A ≠ Set.univ := by
    by_contra hex
    apply hnot
    rw [connectedSpace_iff_clopen]
    refine ⟨hU_nonempty, ?_⟩
    intro A hA
    by_cases hAe : A = ∅
    · exact Or.inl hAe
    · right
      by_contra hAu
      exact hex ⟨A, hA, hAe, hAu⟩
  obtain ⟨A, hAclopen, hAne, hAuniv⟩ := hnontrivialClopen
  let B : Set U := Aᶜ
  let A₀ : Set (PrimeSpectrum D) := Subtype.val '' A
  let B₀ : Set (PrimeSpectrum D) := Subtype.val '' B
  have hAopen : IsOpen A₀ := by
    exact U.isOpen.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen.mp
      hAclopen.isOpen
  have hBopen : IsOpen B₀ := by
    exact U.isOpen.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen.mp
      hAclopen.compl.isOpen
  have hcover :
      A₀ ∪ B₀ =
        ({closedPoint D}ᶜ : Set (PrimeSpectrum D)) := by
    ext p
    constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact a.property
      · exact b.property
    · intro hp
      have hpU : p ∈ U := by
        exact (Scheme.mem_puncturedSpectrumOpen_iff D p).2 <| by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hp
      let pU : U := ⟨p, hpU⟩
      by_cases hpA : pU ∈ A
      · exact Or.inl ⟨pU, hpA, rfl⟩
      · exact Or.inr ⟨pU, hpA, rfl⟩
  have hdisjoint : Disjoint A₀ B₀ := by
    rw [Set.disjoint_left]
    intro p hpA hpB
    obtain ⟨a, ha, rfl⟩ := hpA
    obtain ⟨b, hb, hab⟩ := hpB
    have hab' : a = b := Subtype.ext hab.symm
    exact hb (hab' ▸ ha)
  have hAnonempty : A₀.Nonempty := by
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hAne
    exact ⟨a.1, ⟨a, ha, rfl⟩⟩
  have hBnonempty : B₀.Nonempty := by
    have hB : B.Nonempty := by
      dsimp only [B]
      exact Set.nonempty_compl.mpr hAuniv
    obtain ⟨b, hb⟩ := hB
    exact ⟨b.1, ⟨b, hb, rfl⟩⟩
  exact
    exists_radical_nonmaximal_ambient_componentIntersectionIdeals_of_open_puncture_partition
      hdim x hx hAopen hBopen hcover hdisjoint hAnonempty hBnonempty

/-- If a punctured principal hypersurface is disconnected, its ambient local
ring contains the corresponding pair of proper component-intersection
ideals. -/
theorem exists_ambient_componentIntersectionIdeals_of_not_connectedSpace
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
    ¬ ConnectedSpace
        (Scheme.puncturedSpectrum (C ⧸ Ideal.span {x})) →
      ∃ a b : Ideal C,
        Ideal.span {x} ≤ a ∧ Ideal.span {x} ≤ b ∧
        a ≠ ⊤ ∧ b ≠ ⊤ ∧
        a ≠ maximalIdeal C ∧ b ≠ maximalIdeal C ∧
        a ⊓ b = (Ideal.span {x}).radical ∧
        (a ⊔ b).radical = maximalIdeal C := by
  let D := C ⧸ Ideal.span {x}
  let : Nontrivial D :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing D :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  intro hnot
  obtain ⟨a, b, hxa, hxb, ha, hb, hamax, hbmax, _haRadical,
      _hbRadical, hinf, hradical⟩ :=
    exists_radical_nonmaximal_ambient_componentIntersectionIdeals_of_not_connectedSpace
      hdim x hx hnot
  exact ⟨a, b, hxa, hxb, ha, hb, hamax, hbmax, hinf, hradical⟩

end AlgebraicGeometry.FiniteEtale

end
