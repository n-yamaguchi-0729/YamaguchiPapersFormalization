/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.PuncturedSpectrumHypersurfaceDisconnectedReduction

/-!
# Power data from a disconnected punctured hypersurface

This file converts the ideal-theoretic separation attached to a disconnected
punctured hypersurface into the two power containments used by complete-local
intersection arguments.
-/

noncomputable section

open IsLocalRing

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- If the radical of an ideal is the maximal ideal of a Noetherian local
ring, then a power of the maximal ideal is contained in it. -/
theorem exists_maximalIdeal_pow_le_of_radical_eq
    {C : Type u} [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    {I : Ideal C} (hI : I.radical = maximalIdeal C) :
    ∃ n : ℕ, (maximalIdeal C) ^ n ≤ I := by
  obtain ⟨n, hn⟩ :=
    I.exists_radical_pow_le_of_fg I.radical.fg_of_isNoetherianRing
  exact ⟨n, by simpa only [hI] using hn⟩

/-- If the intersection of two ideals is the radical of `I`, then a power of
their product is contained in `I`. -/
theorem exists_product_pow_le_of_inf_eq_radical
    {C : Type u} [CommRing C] [IsNoetherianRing C]
    {I a b : Ideal C} (hab : a ⊓ b = I.radical) :
    ∃ n : ℕ, (a * b) ^ n ≤ I := by
  apply Ideal.exists_pow_le_of_le_radical_of_fg
  · rw [← hab]
    exact Ideal.mul_le_inf
  · exact (a * b).fg_of_isNoetherianRing

/-- Strengthened power data retaining that both component ideals are radical
and nonmaximal. -/
theorem exists_radical_completeIntersectionPowerData_of_not_connectedSpace
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
      ∃ a b : Ideal C, ∃ n k : ℕ,
        Ideal.span {x} ≤ a ∧ Ideal.span {x} ≤ b ∧
        a ≠ ⊤ ∧ b ≠ ⊤ ∧
        a ≠ maximalIdeal C ∧ b ≠ maximalIdeal C ∧
        a.IsRadical ∧ b.IsRadical ∧
        a ⊓ b = (Ideal.span {x}).radical ∧
        (a ⊔ b).radical = maximalIdeal C ∧
        (maximalIdeal C) ^ n ≤ a ⊔ b ∧
        (a * b) ^ k ≤ Ideal.span {x} := by
  let D := C ⧸ Ideal.span {x}
  let : Nontrivial D :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing D :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  intro hnot
  obtain ⟨a, b, hxa, hxb, ha, hb, ham, hbm, haRadical, hbRadical,
      hinf, hsup⟩ :=
    exists_radical_nonmaximal_ambient_componentIntersectionIdeals_of_not_connectedSpace
      hdim x hx hnot
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_radical_eq hsup
  obtain ⟨k, hk⟩ := exists_product_pow_le_of_inf_eq_radical hinf
  exact
    ⟨a, b, n, k, hxa, hxb, ha, hb, ham, hbm, haRadical, hbRadical,
      hinf, hsup, hn, hk⟩

/-- A disconnected punctured principal hypersurface produces ambient proper
ideals together with the two power containments that a complete-local
intersection theorem must exclude. -/
theorem exists_completeIntersectionPowerData_of_not_connectedSpace
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
      ∃ a b : Ideal C, ∃ n k : ℕ,
        Ideal.span {x} ≤ a ∧ Ideal.span {x} ≤ b ∧
        a ≠ ⊤ ∧ b ≠ ⊤ ∧
        a ≠ maximalIdeal C ∧ b ≠ maximalIdeal C ∧
        a ⊓ b = (Ideal.span {x}).radical ∧
        (a ⊔ b).radical = maximalIdeal C ∧
        (maximalIdeal C) ^ n ≤ a ⊔ b ∧
        (a * b) ^ k ≤ Ideal.span {x} := by
  let D := C ⧸ Ideal.span {x}
  let : Nontrivial D :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing D :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  intro hnot
  obtain ⟨a, b, n, k, hxa, hxb, ha, hb, ham, hbm, _haRadical,
      _hbRadical, hinf, hsup, hn, hk⟩ :=
    exists_radical_completeIntersectionPowerData_of_not_connectedSpace
      hdim x hx hnot
  exact
    ⟨a, b, n, k, hxa, hxb, ha, hb, ham, hbm, hinf, hsup, hn, hk⟩

end AlgebraicGeometry.FiniteEtale

end
