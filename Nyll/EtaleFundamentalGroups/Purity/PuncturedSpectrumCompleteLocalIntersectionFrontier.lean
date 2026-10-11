/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumCompleteLocalDomainAlgebra
import Mathlib.RingTheory.Ideal.UFD

/-!
# The complete-local intersection frontier

Disconnectedness of a punctured principal hypersurface produces two
height-one minimal primes whose supremum has maximal radical.  This file
sharpens the existing height-at-most-one output to exact height one and
identifies the height of the supremum with the dimension of the local ring.

Krull's height theorem then closes the argument when height-one primes are
principal, in particular for a UFD.  For a general complete local domain, the
remaining input is precisely the connectedness/intersection theorem that
replaces this principality step.
-/

noncomputable section

open IsLocalRing TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Taking the radical of an ideal does not change its height. -/
theorem ideal_height_radical_eq
    {R : Type u} [CommRing R] (I : Ideal R) :
    I.radical.height = I.height := by
  rw [I.radical.height_eq_inf_minimalPrimes,
    I.height_eq_inf_minimalPrimes, I.radical_minimalPrimes]

/-- An ideal with maximal radical has height equal to the dimension of a
local ring. -/
theorem ideal_height_eq_ringKrullDim_of_radical_eq_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.radical = maximalIdeal R) :
    ((I.height : ℕ∞) : WithBot ℕ∞) = ringKrullDim R := by
  calc
    ((I.height : ℕ∞) : WithBot ℕ∞) = I.radical.height := by
      rw [ideal_height_radical_eq]
    _ = (maximalIdeal R).height :=
      congrArg (fun J : Ideal R => ((J.height : ℕ∞) : WithBot ℕ∞)) hI
    _ = ringKrullDim R := IsLocalRing.maximalIdeal_height_eq_ringKrullDim

/-- A disconnected punctured principal hypersurface in a local domain of
dimension at least three produces two distinct height-one minimal primes.
Their supremum has height equal to the full dimension, hence at least three. -/
theorem exists_height_one_minimalPrime_pair_of_not_connectedSpace
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
          P ≠ Q ∧ P.height = 1 ∧ Q.height = 1 ∧
          (P ⊔ Q).radical = maximalIdeal C ∧
          ((P ⊔ Q).height : WithBot ℕ∞) = ringKrullDim C ∧
          (3 : ℕ∞) ≤ (P ⊔ Q).height := by
  let D := C ⧸ Ideal.span {x}
  let : Nontrivial D :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing D :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  intro hnot
  obtain ⟨hx0, P, Q, hP, hQ, hPMax, hQMax, hPheight, hQheight,
      hPQ⟩ :=
    exists_height_le_one_minimalPrime_pair_of_not_connectedSpace
      hdim x hx hnot
  let : P.IsPrime := hP.isPrime
  let : Q.IsPrime := hQ.isPrime
  have hspanHeight : 1 ≤ (Ideal.span {x}).height :=
    Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hx0)
  have hPheight' : P.height = 1 :=
    le_antisymm hPheight (hspanHeight.trans (Ideal.height_mono hP.le))
  have hQheight' : Q.height = 1 :=
    le_antisymm hQheight (hspanHeight.trans (Ideal.height_mono hQ.le))
  have hPneQ : P ≠ Q := by
    intro h
    apply hPMax
    subst Q
    simpa only [sup_idem, hP.isPrime.isRadical.radical] using hPQ
  have hSupHeight :
      (((P ⊔ Q).height : ℕ∞) : WithBot ℕ∞) = ringKrullDim C :=
    ideal_height_eq_ringKrullDim_of_radical_eq_maximalIdeal (P ⊔ Q) hPQ
  have hThree : (3 : ℕ∞) ≤ (P ⊔ Q).height := by
    have hdim' := hdim
    rw [← hSupHeight] at hdim'
    exact WithBot.coe_le_coe.mp hdim'
  exact ⟨hx0, P, Q, hP, hQ, hPMax, hQMax, hPneQ,
    hPheight', hQheight', hPQ, hSupHeight, hThree⟩

/-- If two ideals are principal, Krull's height theorem bounds the height of
their supremum by two. -/
theorem ideal_height_sup_le_two_of_isPrincipal
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (P Q : Ideal R) (hP : P.IsPrincipal) (hQ : Q.IsPrincipal)
    (hPQ : P ⊔ Q ≠ ⊤) :
    (P ⊔ Q).height ≤ 2 := by
  obtain ⟨p, hp⟩ := hP
  obtain ⟨q, hq⟩ := hQ
  have hspan : P ⊔ Q = Ideal.span ({p, q} : Set R) := by
    rw [hp, hq, ← Ideal.span_union]
    congr 1
  rw [hspan] at hPQ ⊢
  refine (Ideal.height_le_spanFinrank _ hPQ).trans ?_
  refine (Submodule.spanFinrank_span_le_encard ({p, q} : Set R)).trans ?_
  calc
    ({p, q} : Set R).encard ≤ ({q} : Set R).encard + 1 :=
      Set.encard_insert_le {q} p
    _ = 2 := by norm_num

/-- In a Noetherian UFD, the supremum of two height-one prime ideals has
height at most two whenever it is proper. -/
theorem ideal_height_sup_le_two_of_height_one_of_uniqueFactorizationMonoid
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [UniqueFactorizationMonoid R]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hP : P.height = 1) (hQ : Q.height = 1)
    (hPQ : P ⊔ Q ≠ ⊤) :
    (P ⊔ Q).height ≤ 2 :=
  ideal_height_sup_le_two_of_isPrincipal P Q
    (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hP)
    (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hQ) hPQ

/-- Krull's height theorem proves connectedness of a punctured principal
hypersurface in a Noetherian local UFD of dimension at least three. -/
theorem connectedSpace_puncturedSpectrum_quotient_span_singleton_of_ufd
    {C : Type u} [CommRing C] [IsDomain C] [IsLocalRing C]
    [IsNoetherianRing C] [UniqueFactorizationMonoid C]
    (hdim : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C)
    (x : C) (hx : x ∈ maximalIdeal C) :
    letI : Nontrivial (C ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
          (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
    letI : IsLocalRing (C ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective
    ConnectedSpace
      (Scheme.puncturedSpectrum (C ⧸ Ideal.span {x})) := by
  let D := C ⧸ Ideal.span {x}
  let : Nontrivial D :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing D :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  by_contra hnot
  obtain ⟨_hx0, P, Q, _hP, _hQ, _hPMax, _hQMax, _hPneQ,
      hPheight, hQheight, hPQ, _hSupHeight, hThree⟩ :=
    exists_height_one_minimalPrime_pair_of_not_connectedSpace
      hdim x hx hnot
  let : P.IsPrime := _hP.isPrime
  let : Q.IsPrime := _hQ.isPrime
  have hProper : P ⊔ Q ≠ ⊤ := by
    intro htop
    apply (maximalIdeal.isMaximal C).ne_top
    simp only [← hPQ, htop, Ideal.radical_top]
  have hTwo : (P ⊔ Q).height ≤ 2 :=
    ideal_height_sup_le_two_of_height_one_of_uniqueFactorizationMonoid
      P Q hPheight hQheight hProper
  have : (3 : ℕ∞) ≤ 2 := hThree.trans hTwo
  norm_num at this

end AlgebraicGeometry.FiniteEtale

end
