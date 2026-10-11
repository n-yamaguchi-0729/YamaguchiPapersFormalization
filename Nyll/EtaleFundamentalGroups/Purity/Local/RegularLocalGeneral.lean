/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular hypersurface sections of regular local domains

The induction on dimension in local purity cuts a regular local ring by a
parameter whose cotangent class is nonzero.  This file supplies the local
algebra behind that step in arbitrary dimension: quotienting a regular local
domain by an element of the maximal ideal which is not in its square again
gives a regular local ring.

The proof does not choose a full regular system of parameters.  It extends the
nonzero cotangent class to a basis, lifts the remaining basis vectors, and uses
Nakayama to generate the maximal ideal after quotienting.  The principal
non-zero-divisor dimension formula then identifies the dimension of the
quotient.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing

universe u

/-- A hypersurface cut by a nonzero cotangent vector in a regular local domain
is regular local.  This is valid in every finite Krull dimension. -/
theorem isRegularLocalRing_quotient_span_singleton_of_not_mem_maximalIdeal_sq
    {R : Type u} [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    {x : R} (hxMem : x ∈ maximalIdeal R)
    (hxSq : x ∉ maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  classical
  let m : Ideal R := maximalIdeal R
  let I : Ideal R := Ideal.span ({x} : Set R)
  let S := R ⧸ I
  have hIle : I ≤ m := by
    apply Ideal.span_le.mpr
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    change x ∈ maximalIdeal R
    exact hxMem
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIle
  let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective R S (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let x' : m := ⟨x, by simpa only [m] using hxMem⟩
  have hxCot : m.toCotangent x' ≠ 0 := by
    intro hzero
    exact hxSq (by
      simpa only [m, x'] using (m.toCotangent_eq_zero x').mp hzero)
  let hs : LinearIndepOn (ResidueField R) id {m.toCotangent x'} :=
    ((linearIndepOn_singleton_iff (ResidueField R)).mpr hxCot)
  let b := Module.Basis.extend hs
  let ι := hs.extend (Set.subset_univ {m.toCotangent x'})
  let ix : ι :=
    ⟨m.toCotangent x', hs.subset_extend _ (Set.mem_singleton _)⟩
  let : Fintype ι := Fintype.ofFinite ι
  let restFinset : Finset ι := Finset.univ.erase ix
  let rest : Set ι := ↑restFinset
  let lift (i : ι) : m :=
    Classical.choose (m.toCotangent_surjective (b i))
  have hlift (i : ι) : m.toCotangent (lift i) = b i :=
    Classical.choose_spec (m.toCotangent_surjective (b i))
  have hbix : b ix = m.toCotangent x' := by
    simpa only [b, ix] using Module.Basis.extend_apply_self hs ix
  let lifts : Set m := lift '' rest
  have hcotangentImage :
      m.toCotangent '' (insert x' lifts) = Set.range b := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with rfl | ⟨i, hi, rfl⟩
      · refine ⟨ix, ?_⟩
        exact hbix
      · refine ⟨i, ?_⟩
        exact (hlift i).symm
    · rintro ⟨i, rfl⟩
      by_cases hi : i = ix
      · subst i
        refine ⟨x', Set.mem_insert _ _, ?_⟩
        exact hbix.symm
      · have hLiftMem : lift i ∈ lifts := by
          have hiRest : i ∈ rest := by
            change i ∈ Finset.univ.erase ix
            exact Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
          exact ⟨i, hiRest, rfl⟩
        exact ⟨lift i, Or.inr hLiftMem, hlift i⟩
  have hcotangentSpan :
      Submodule.span (ResidueField R)
          (m.toCotangent '' (insert x' lifts)) = ⊤ := by
    rw [hcotangentImage]
    exact b.span_eq
  have hliftsSpan : Submodule.span R (insert x' lifts) = ⊤ :=
    (CotangentSpace.span_image_eq_top_iff (R := R)).mp hcotangentSpan
  let liftValues : Set R := m.subtype '' lifts
  have hspanR : Ideal.span (insert x liftValues) = m := by
    change Submodule.span R (insert x liftValues) = m
    calc
      Submodule.span R (insert x liftValues) =
          (Submodule.span R (insert x' lifts)).map m.subtype := by
        rw [Submodule.map_span]
        congr 1
        ext y
        simp only [Set.mem_image, Set.mem_insert_iff, liftValues]
        constructor
        · rintro (rfl | ⟨z, hz, rfl⟩)
          · exact ⟨x', Or.inl rfl, rfl⟩
          · exact ⟨z, Or.inr hz, rfl⟩
        · rintro ⟨z, rfl | hz, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨z, hz, rfl⟩
      _ = (⊤ : Submodule R m).map m.subtype := by rw [hliftsSpan]
      _ = m := by rw [Submodule.map_top, Submodule.range_subtype]
  let q : R →+* S := Ideal.Quotient.mk I
  have hqx : q x = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton_self x
  have hspanS : Ideal.span (q '' liftValues) = maximalIdeal S := by
    calc
      Ideal.span (q '' liftValues) =
          Ideal.span (insert (q x) (q '' liftValues)) := by simp only [hqx, Ideal.span_insert_zero]
      _ = Ideal.span (q '' (insert x liftValues)) := by rw [Set.image_insert_eq]
      _ = (Ideal.span (insert x liftValues)).map q := by
        rw [Ideal.map_span]
      _ = m.map q := by rw [hspanR]
      _ = maximalIdeal S :=
        IsLocalRing.map_maximalIdeal_of_surjective q
          Ideal.Quotient.mk_surjective
  have hliftValuesFinite : liftValues.Finite := by
    exact (Set.toFinite rest).image lift |>.image m.subtype
  have hquotientGeneratorsFinite : (q '' liftValues).Finite :=
    hliftValuesFinite.image q
  have hspanFinrankS :
      (maximalIdeal S).spanFinrank ≤ rest.ncard := by
    rw [← hspanS]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite
      hquotientGeneratorsFinite).trans ?_
    refine (Set.ncard_image_le (f := q) hliftValuesFinite).trans ?_
    refine (Set.ncard_image_le (f := m.subtype)
      ((Set.toFinite rest).image lift)).trans ?_
    exact Set.ncard_image_le (f := lift) (Set.toFinite rest)
  have hrestCard : rest.ncard + 1 = Fintype.card ι := by
    simpa only [rest, restFinset, Set.ncard_coe_finset,
      Finset.card_univ] using
      (Finset.card_erase_add_one (s := (Finset.univ : Finset ι))
        (a := ix) (Finset.mem_univ ix))
  have hindexCard : Fintype.card ι =
      Module.finrank (ResidueField R) (CotangentSpace R) := by
    exact (Module.finrank_eq_card_basis b).symm
  have hspanFinrankSucc :
      (maximalIdeal S).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by
    calc
      (maximalIdeal S).spanFinrank + 1 ≤ rest.ncard + 1 :=
        Nat.add_le_add_right hspanFinrankS 1
      _ = Fintype.card ι := hrestCard
      _ = Module.finrank (ResidueField R) (CotangentSpace R) := by
        exact hindexCard
      _ = (maximalIdeal R).spanFinrank :=
        (spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R).symm
  have hxNe : x ≠ 0 := by
    intro hx
    apply hxSq
    simp only [hx, zero_mem]
  have hxRegular : IsSMulRegular R x := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro a ha
    have hxa : x * a = 0 := by simpa only [smul_eq_mul] using ha
    exact (mul_eq_zero.mp hxa).resolve_left hxNe
  have hdimSucc : ringKrullDim S + 1 = ringKrullDim R := by
    simpa only [S, I] using
      ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
        hxRegular hxMem
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  apply (ENat.WithBot.add_le_add_natCast_right_iff (c := 1)).mp
  have hcast :
      (((maximalIdeal S).spanFinrank + 1 : ℕ) : WithBot ℕ∞) ≤
        ((maximalIdeal R).spanFinrank : WithBot ℕ∞) := by
    exact_mod_cast hspanFinrankSucc
  calc
    ((maximalIdeal S).spanFinrank : WithBot ℕ∞) + 1 =
        (((maximalIdeal S).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
      norm_num
    _ ≤ ((maximalIdeal R).spanFinrank : WithBot ℕ∞) := hcast
    _ = ringKrullDim R := IsRegularLocalRing.spanFinrank_maximalIdeal
    _ = ringKrullDim S + 1 := hdimSucc.symm

/-- A positive-dimensional regular local domain contains a parameter whose
principal quotient is again regular local.  The parameter and its
transversality to the square of the maximal ideal are produced internally
from a nonzero cotangent vector. -/
theorem exists_parameter_with_regularLocalRing_quotient
    {R : Type u} [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim R) :
    ∃ x : R, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧
      IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  let m : Ideal R := maximalIdeal R
  have hfin :
      0 < Module.finrank (ResidueField R) (CotangentSpace R) := by
    have hreg :=
      (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp
        (inferInstance : IsRegularLocalRing R)
    rw [← hreg] at hdim
    exact_mod_cast hdim
  obtain ⟨z, hz⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.mp hfin
  obtain ⟨x', hx'⟩ := m.toCotangent_surjective z
  let x : R := x'
  have hxMem : x ∈ maximalIdeal R := x'.property
  have hxSq : x ∉ maximalIdeal R ^ 2 := by
    intro hxSquare
    apply hz
    rw [← hx']
    exact (m.toCotangent_eq_zero x').mpr (by
      simpa only [m, x] using hxSquare)
  exact ⟨x, hxMem, hxSq,
    isRegularLocalRing_quotient_span_singleton_of_not_mem_maximalIdeal_sq
      hxMem hxSq⟩

/-- Cutting a regular local domain of dimension `n + 1` by the parameter
constructed above gives a regular local ring of dimension exactly `n`.
This is the dimension-decreasing datum used by induction in local purity. -/
theorem exists_parameter_with_regularLocalRing_quotient_ringKrullDim_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (n : ℕ)
    (hdim : ringKrullDim R = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ x : R, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧
      IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) =
        (n : WithBot ℕ∞) := by
  have hpositive : (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
    rw [hdim]
    exact_mod_cast Nat.le_add_left 1 n
  obtain ⟨x, hxMem, hxSq, hregularQuotient⟩ :=
    exists_parameter_with_regularLocalRing_quotient hpositive
  have hxNe : x ≠ 0 := by
    intro hx
    apply hxSq
    simp only [hx, zero_mem]
  have hxRegular : IsSMulRegular R x := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro a ha
    have hxa : x * a = 0 := by simpa only [smul_eq_mul] using ha
    exact (mul_eq_zero.mp hxa).resolve_left hxNe
  have hdimSucc :
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 =
        ringKrullDim R :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
      hxRegular hxMem
  have hdimQuotient :
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) =
        (n : WithBot ℕ∞) := by
    apply ENat.WithBot.add_one_cancel.mp
    calc
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 =
          ringKrullDim R := hdimSucc
      _ = ((n + 1 : ℕ) : WithBot ℕ∞) := hdim
      _ = (n : WithBot ℕ∞) + 1 := by norm_num
  exact ⟨x, hxMem, hxSq, hregularQuotient, hdimQuotient⟩

/-- In dimension at least three, one can choose the regular parameter so that
the regular local quotient still has dimension at least two.  This is the
purely algebraic induction step preceding the local extension theorem. -/
theorem exists_parameter_with_regularLocalRing_quotient_of_three_le_ringKrullDim
    {R : Type u} [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (hdim : (3 : WithBot ℕ∞) ≤ ringKrullDim R) :
    ∃ x : R, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧
      IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) ∧
      (2 : WithBot ℕ∞) ≤
        ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) := by
  let d : ℕ := (maximalIdeal R).spanFinrank
  have hregularDimension : (d : WithBot ℕ∞) = ringKrullDim R := by
    exact IsRegularLocalRing.spanFinrank_maximalIdeal
  have hthree : 3 ≤ d := by
    rw [← hregularDimension] at hdim
    exact_mod_cast hdim
  let n : ℕ := d - 1
  have hd : d = n + 1 := by
    dsimp only [n]
    omega
  have hdimSuccessor :
      ringKrullDim R = ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hregularDimension, hd]
  obtain ⟨x, hxMem, hxSq, hregularQuotient, hdimQuotient⟩ :=
    exists_parameter_with_regularLocalRing_quotient_ringKrullDim_eq
      n hdimSuccessor
  have hn : 2 ≤ n := by
    dsimp only [n]
    omega
  refine ⟨x, hxMem, hxSq, hregularQuotient, ?_⟩
  rw [hdimQuotient]
  exact_mod_cast hn

end EtaleFundamentalGroups

end
