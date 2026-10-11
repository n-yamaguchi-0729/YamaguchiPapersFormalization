/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedLefschetzAlgebra
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Components of a punctured principal hypersurface

For a Noetherian local domain of dimension at least three, no irreducible
component of a principal hypersurface is supported only at the closed point.
Equivalently, every irreducible component of the quotient spectrum meets its
puncture.  This is the component-theoretic input preceding the complete-local
intersection theorem.
-/

noncomputable section

open IsLocalRing TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- An irreducible component that meets an open set lies entirely on one
side of any disjoint open partition of that open set. -/
theorem irreducibleComponent_inter_subset_partition_side
    {X : Type u} [TopologicalSpace X]
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
    {U A B : Set X} (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = U) (hdisjoint : Disjoint A B) :
    Z ∩ U ⊆ A ∨ Z ∩ U ⊆ B := by
  classical
  by_cases hleft : Z ∩ U ⊆ A
  · exact Or.inl hleft
  · right
    obtain ⟨y, hyZU, hyA⟩ := Set.not_subset.mp hleft
    have hyB : y ∈ B := by
      have hyAB : y ∈ A ∪ B := hcover.symm ▸ hyZU.2
      exact hyAB.resolve_left hyA
    intro z hzZU
    by_contra hzB
    have hzA : z ∈ A := by
      have hzAB : z ∈ A ∪ B := hcover.symm ▸ hzZU.2
      exact hzAB.resolve_right hzB
    obtain ⟨w, hwZ, hwAB⟩ :=
      hZ.1.2 A B hA hB ⟨z, hzZU.1, hzA⟩ ⟨y, hyZU.1, hyB⟩
    exact Set.disjoint_left.mp hdisjoint hwAB.1 hwAB.2

/-- Components assigned to opposite sides of a disjoint partition can meet
only outside the partitioned open set. -/
theorem inter_subset_compl_of_component_partition_sides
    {X : Type u} {Z W U A B : Set X}
    (hZ : Z ∩ U ⊆ A) (hW : W ∩ U ⊆ B)
    (hdisjoint : Disjoint A B) :
    Z ∩ W ⊆ Uᶜ := by
  intro z hzZW hzU
  exact Set.disjoint_left.mp hdisjoint
    (hZ ⟨hzZW.1, hzU⟩) (hW ⟨hzZW.2, hzU⟩)

/-- A minimal prime over a principal ideal in a local ring of dimension at
least three cannot be the maximal ideal. -/
theorem minimalPrime_span_singleton_ne_maximalIdeal
    {C : Type u} [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    (hdim : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C)
    (x : C) (P : Ideal C) (hP : P ∈ (Ideal.span {x}).minimalPrimes) :
    P ≠ maximalIdeal C := by
  intro hPmax
  have hheight : P.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span {x}) P hP
  have hdim' : ((3 : ℕ∞) : WithBot ℕ∞) ≤
      ((P.height : ℕ∞) : WithBot ℕ∞) := by
    rw [hPmax, IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact hdim
  have : ((3 : ℕ∞) : WithBot ℕ∞) ≤
      ((1 : ℕ∞) : WithBot ℕ∞) :=
    hdim'.trans (WithBot.coe_le_coe.mpr hheight)
  norm_num at this

/-- A minimal prime of a principal quotient in dimension at least three is
not the quotient maximal ideal. -/
theorem minimalPrime_quotient_span_singleton_ne_maximalIdeal
    {C : Type u} [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    (hdim : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C)
    (x : C) (hx : x ∈ maximalIdeal C)
    (Q : Ideal (C ⧸ Ideal.span {x}))
    (hQ : Q ∈ minimalPrimes (C ⧸ Ideal.span {x})) :
    letI : Nontrivial (C ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
          (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
    letI : IsLocalRing (C ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective
    Q ≠ maximalIdeal (C ⧸ Ideal.span {x}) := by
  let I : Ideal C := Ideal.span {x}
  let q : C →+* C ⧸ I := Ideal.Quotient.mk I
  have hIle : I ≤ maximalIdeal C :=
    (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : Nontrivial (C ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top hIle
  let : IsLocalRing (C ⧸ I) :=
    IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  let : IsLocalHom q :=
    IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have hcomap : Q.comap q ∈ I.minimalPrimes := by
    have hQ' : Q ∈ (⊥ : Ideal (C ⧸ I)).minimalPrimes := hQ
    have := Ideal.minimalPrimes_comap_of_surjective
      Ideal.Quotient.mk_surjective hQ'
    simpa only [← RingHom.ker_eq_comap_bot, q, Ideal.mk_ker] using this
  intro hQmax
  apply minimalPrime_span_singleton_ne_maximalIdeal hdim x (Q.comap q) hcomap
  rw [hQmax]
  exact IsLocalRing.maximalIdeal_comap q

/-- Every irreducible component of a principal quotient in dimension at
least three contains a point different from the closed point. -/
theorem irreducibleComponent_quotient_span_singleton_inter_puncture_nonempty
    {C : Type u} [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    (hdim : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C)
    (x : C) (hx : x ∈ maximalIdeal C)
    (Z : Set (PrimeSpectrum (C ⧸ Ideal.span {x})))
    (hZ : Z ∈ irreducibleComponents (PrimeSpectrum (C ⧸ Ideal.span {x}))) :
    letI : Nontrivial (C ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
          (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
    letI : IsLocalRing (C ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective
    (Z ∩ ({closedPoint (C ⧸ Ideal.span {x})}ᶜ :
      Set (PrimeSpectrum (C ⧸ Ideal.span {x})))).Nonempty := by
  let B := C ⧸ Ideal.span {x}
  let : Nontrivial B :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing B :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  let Q : Ideal B := PrimeSpectrum.vanishingIdeal Z
  have hQ : Q ∈ minimalPrimes B := by
    rw [← PrimeSpectrum.vanishingIdeal_irreducibleComponents B]
    exact ⟨Z, hZ, rfl⟩
  let : Q.IsPrime := hQ.isPrime
  let q : PrimeSpectrum B := ⟨Q, inferInstance⟩
  have hqZ : q ∈ Z := by
    have hclosed : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
    have hzero : PrimeSpectrum.zeroLocus Q = Z := by
      change PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal Z) = Z
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
        hclosed.closure_eq]
    rw [← hzero]
    exact show Q ≤ q.asIdeal from le_rfl
  have hqne : q ≠ closedPoint B := by
    intro hq
    apply minimalPrime_quotient_span_singleton_ne_maximalIdeal hdim x hx Q hQ
    exact congrArg PrimeSpectrum.asIdeal hq
  refine ⟨q, hqZ, ?_⟩
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hqne

end AlgebraicGeometry.FiniteEtale

end
