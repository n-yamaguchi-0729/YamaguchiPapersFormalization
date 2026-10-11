/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumHypersurfaceSeparation

/-!
# Ambient ideals from a punctured hypersurface separation

The component-intersection ideals attached to a separation of a principal
hypersurface can be pulled back through the quotient map.  This gives two
proper ideals of the ambient local ring whose intersection is the radical of
the principal ideal and whose sum is primary to the maximal ideal.
-/

noncomputable section

open IsLocalRing TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- A nontrivial open separation of a punctured principal hypersurface gives
the ambient ideal configuration used in complete-local intersection
theorems. -/
theorem exists_ambient_componentIntersectionIdeals_of_open_puncture_partition
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
      ∃ a b : Ideal C,
        Ideal.span {x} ≤ a ∧ Ideal.span {x} ≤ b ∧
        a ≠ ⊤ ∧ b ≠ ⊤ ∧
        a ⊓ b = (Ideal.span {x}).radical ∧
        (a ⊔ b).radical = maximalIdeal C := by
  let I : Ideal C := Ideal.span {x}
  let D := C ⧸ I
  let q : C →+* D := Ideal.Quotient.mk I
  let : Nontrivial D :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing D :=
    IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  let : IsLocalHom q :=
    IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  intro A₀ B₀ hAopen hBopen hcover hdisjoint hAnonempty hBnonempty
  obtain ⟨a, b, ha, hb, hinf, hradical⟩ :=
    exists_proper_componentIntersectionIdeals_of_open_puncture_partition
      hdim x hx hAopen hBopen hcover hdisjoint hAnonempty hBnonempty
  let A : Ideal C := a.comap q
  let B : Ideal C := b.comap q
  have hIA : I ≤ A := by
    rw [← Ideal.mk_ker (I := I), RingHom.ker_eq_comap_bot]
    exact Ideal.comap_mono bot_le
  have hIB : I ≤ B := by
    rw [← Ideal.mk_ker (I := I), RingHom.ker_eq_comap_bot]
    exact Ideal.comap_mono bot_le
  have hA : A ≠ ⊤ := Ideal.comap_ne_top q ha
  have hB : B ≠ ⊤ := Ideal.comap_ne_top q hb
  have hABinf : A ⊓ B = I.radical := by
    calc
      A ⊓ B = Ideal.comap q (a ⊓ b) := (Ideal.comap_inf q a b).symm
      _ = Ideal.comap q (nilradical D) := by rw [hinf]
      _ = Ideal.comap q (Ideal.radical ⊥) := rfl
      _ = Ideal.radical (Ideal.comap q ⊥) := Ideal.comap_radical q ⊥
      _ = I.radical := by
        rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hcomapSup : Ideal.comap q (a ⊔ b) = A ⊔ B := by
    calc
      Ideal.comap q (a ⊔ b) =
          Ideal.comap q ((A ⊔ B).map q) := by
        congr 1
        dsimp only [A, B]
        exact (Ideal.map_sup_comap_of_surjective q
          Ideal.Quotient.mk_surjective a b).symm
      _ = (A ⊔ B) ⊔ Ideal.comap q ⊥ :=
        Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective (A ⊔ B)
      _ = A ⊔ B := by
        rw [sup_eq_left]
        exact (Ideal.comap_mono bot_le).trans le_sup_left
  have hABradical : (A ⊔ B).radical = maximalIdeal C := by
    have h := congrArg (Ideal.comap q) hradical
    rw [Ideal.comap_radical, hcomapSup,
      IsLocalRing.maximalIdeal_comap q] at h
    exact h
  exact ⟨A, B, hIA, hIB, hA, hB, hABinf, hABradical⟩

/-- Ambient form retaining the source-produced fact that both component
ideals are radical and nonmaximal. -/
theorem exists_radical_nonmaximal_ambient_componentIntersectionIdeals_of_open_puncture_partition
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
      ∃ a b : Ideal C,
        Ideal.span {x} ≤ a ∧ Ideal.span {x} ≤ b ∧
        a ≠ ⊤ ∧ b ≠ ⊤ ∧
        a ≠ maximalIdeal C ∧ b ≠ maximalIdeal C ∧
        a.IsRadical ∧ b.IsRadical ∧
        a ⊓ b = (Ideal.span {x}).radical ∧
        (a ⊔ b).radical = maximalIdeal C := by
  let I : Ideal C := Ideal.span {x}
  let D := C ⧸ I
  let q : C →+* D := Ideal.Quotient.mk I
  let : Nontrivial D :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing D :=
    IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  let : IsLocalHom q :=
    IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  intro A₀ B₀ hAopen hBopen hcover hdisjoint hAnonempty hBnonempty
  obtain ⟨a, b, ha, hb, hamax, hbmax, haRadical, hbRadical,
      hinf, hradical⟩ :=
    exists_radical_nonmaximal_componentIntersectionIdeals_of_open_puncture_partition
      hdim x hx hAopen hBopen hcover hdisjoint hAnonempty hBnonempty
  let A : Ideal C := a.comap q
  let B : Ideal C := b.comap q
  have hIA : I ≤ A := by
    rw [← Ideal.mk_ker (I := I), RingHom.ker_eq_comap_bot]
    exact Ideal.comap_mono bot_le
  have hIB : I ≤ B := by
    rw [← Ideal.mk_ker (I := I), RingHom.ker_eq_comap_bot]
    exact Ideal.comap_mono bot_le
  have hA : A ≠ ⊤ := Ideal.comap_ne_top q ha
  have hB : B ≠ ⊤ := Ideal.comap_ne_top q hb
  have hAmax : A ≠ maximalIdeal C := by
    intro h
    apply hamax
    calc
      a = A.map q :=
        (Ideal.map_comap_of_surjective q
          Ideal.Quotient.mk_surjective a).symm
      _ = (maximalIdeal C).map q := congrArg (Ideal.map q) h
      _ = maximalIdeal D :=
        IsLocalRing.map_maximalIdeal_of_surjective q
          Ideal.Quotient.mk_surjective
  have hBmax : B ≠ maximalIdeal C := by
    intro h
    apply hbmax
    calc
      b = B.map q :=
        (Ideal.map_comap_of_surjective q
          Ideal.Quotient.mk_surjective b).symm
      _ = (maximalIdeal C).map q := congrArg (Ideal.map q) h
      _ = maximalIdeal D :=
        IsLocalRing.map_maximalIdeal_of_surjective q
          Ideal.Quotient.mk_surjective
  have hARadical : A.IsRadical := by
    dsimp only [A]
    exact haRadical.comap q
  have hBRadical : B.IsRadical := by
    dsimp only [B]
    exact hbRadical.comap q
  have hABinf : A ⊓ B = I.radical := by
    calc
      A ⊓ B = Ideal.comap q (a ⊓ b) := (Ideal.comap_inf q a b).symm
      _ = Ideal.comap q (nilradical D) := by rw [hinf]
      _ = Ideal.comap q (Ideal.radical ⊥) := rfl
      _ = Ideal.radical (Ideal.comap q ⊥) := Ideal.comap_radical q ⊥
      _ = I.radical := by
        rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hcomapSup : Ideal.comap q (a ⊔ b) = A ⊔ B := by
    calc
      Ideal.comap q (a ⊔ b) =
          Ideal.comap q ((A ⊔ B).map q) := by
        congr 1
        dsimp only [A, B]
        exact (Ideal.map_sup_comap_of_surjective q
          Ideal.Quotient.mk_surjective a b).symm
      _ = (A ⊔ B) ⊔ Ideal.comap q ⊥ :=
        Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective (A ⊔ B)
      _ = A ⊔ B := by
        rw [sup_eq_left]
        exact (Ideal.comap_mono bot_le).trans le_sup_left
  have hABradical : (A ⊔ B).radical = maximalIdeal C := by
    have h := congrArg (Ideal.comap q) hradical
    rw [Ideal.comap_radical, hcomapSup,
      IsLocalRing.maximalIdeal_comap q] at h
    exact h
  exact
    ⟨A, B, hIA, hIB, hA, hB, hAmax, hBmax, hARadical, hBRadical,
      hABinf, hABradical⟩

/-- Ambient form retaining that neither component-intersection ideal is the
maximal ideal. -/
theorem exists_nonmaximal_ambient_componentIntersectionIdeals_of_open_puncture_partition
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
  intro A₀ B₀ hAopen hBopen hcover hdisjoint hAnonempty hBnonempty
  obtain ⟨a, b, hxa, hxb, ha, hb, hamax, hbmax, _haRadical,
      _hbRadical, hinf, hradical⟩ :=
    exists_radical_nonmaximal_ambient_componentIntersectionIdeals_of_open_puncture_partition
      hdim x hx hAopen hBopen hcover hdisjoint hAnonempty hBnonempty
  exact ⟨a, b, hxa, hxb, ha, hb, hamax, hbmax, hinf, hradical⟩

end AlgebraicGeometry.FiniteEtale

end
