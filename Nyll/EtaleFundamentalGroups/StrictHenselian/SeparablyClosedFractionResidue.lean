/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Residue fields of normal domains with separably closed fraction field

An irreducible residue polynomial lifts to a monic polynomial over the normal
domain. Gauss's lemma transports irreducibility to its fraction field. A
nonzero derivative forces degree one there. Otherwise, adding a nonzero
element of the maximal ideal times `X` preserves the residue polynomial and
makes the derivative nonzero.

Reference: Stacks Project, Tag 0BSP.
https://stacks.math.columbia.edu/tag/0BSP
-/

namespace EtaleFundamentalGroups.StrictHenselian

open Polynomial
open scoped nonZeroDivisors

universe u v

/-- A monic irreducible polynomial over a normal domain with separably
closed fraction field is linear if its derivative is nonzero. -/
theorem natDegree_eq_one_of_monic_irreducible_derivative_ne_zero
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] [IsSepClosed K]
    (f : R[X]) (hf : f.Monic) (hirr : Irreducible f) (hder : f.derivative ≠ 0) :
    f.natDegree = 1 := by
  have hK : Irreducible (f.map (algebraMap R K)) :=
    (hf.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hirr
  have hKder : (f.map (algebraMap R K)).derivative ≠ 0 := by
    rw [Polynomial.derivative_map]
    intro h
    apply hder
    apply Polynomial.map_injective _ (IsFractionRing.injective R K)
    simpa only [Polynomial.map_zero] using h
  have hdegree := IsSepClosed.degree_eq_one_of_irreducible K hK
    ((Polynomial.separable_iff_derivative_ne_zero hK).mpr hKder)
  have hnat := Polynomial.natDegree_eq_of_degree_eq_some hdegree
  rw [hf.natDegree_map] at hnat
  exact hnat

/-- A normal local domain with separably closed fraction field and a nonzero
maximal ideal has an algebraically closed residue field. -/
theorem isAlgClosed_residueField_of_isSepClosed_fractionRing
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] [IsSepClosed K]
    (hm : IsLocalRing.maximalIdeal R ≠ ⊥) :
    IsAlgClosed (IsLocalRing.ResidueField R) := by
  apply IsAlgClosed.of_exists_root
  intro p hp hpirr
  obtain ⟨f, hfp, hdegree, hf⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective (IsLocalRing.residue_surjective (R := R)) p) hp
  have hfirr : Irreducible f :=
    Polynomial.Monic.irreducible_of_irreducible_map (IsLocalRing.residue R) f hf
      (hfp.symm ▸ hpirr)
  have hfone : f.natDegree = 1 := by
    by_cases hder : f.derivative = 0
    · by_contra hne
      have hpos : 0 < f.natDegree := by
        rw [hdegree]
        exact Polynomial.natDegree_pos_iff_degree_pos.mpr
          (Polynomial.degree_pos_of_irreducible hpirr)
      have hlarge : 1 < f.natDegree := by omega
      obtain ⟨a, ha, ha0⟩ := (IsLocalRing.maximalIdeal R).ne_bot_iff.mp hm
      let g : R[X] := f + C a * X
      have hsmall : (C a * X).degree < f.degree := by
        rw [Polynomial.degree_C_mul_X ha0, Polynomial.degree_eq_natDegree hf.ne_zero]
        exact WithBot.coe_lt_coe.mpr hlarge
      have hg : g.Monic := hf.add_of_left hsmall
      have hgmap : g.map (IsLocalRing.residue R) = p := by
        have hares : IsLocalRing.residue R a = 0 :=
          (Ideal.Quotient.eq_zero_iff_mem).mpr ha
        simp only [g, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_X, hares, Polynomial.C_0, zero_mul, add_zero, hfp]
      have hgirr : Irreducible g :=
        Polynomial.Monic.irreducible_of_irreducible_map (IsLocalRing.residue R) g hg
          (hgmap.symm ▸ hpirr)
      have hgder : g.derivative ≠ 0 := by
        simp only [g, Polynomial.derivative_add, hder, Polynomial.derivative_mul,
          Polynomial.derivative_C, Polynomial.derivative_X, zero_mul, mul_one, zero_add]
        exact Polynomial.C_ne_zero.mpr ha0
      have hgone := natDegree_eq_one_of_monic_irreducible_derivative_ne_zero
        K g hg hgirr hgder
      have hgnat : g.natDegree = f.natDegree :=
        Polynomial.natDegree_add_eq_left_of_degree_lt hsmall
      exact hne (hgnat.symm.trans hgone)
    · exact natDegree_eq_one_of_monic_irreducible_derivative_ne_zero K f hf hfirr hder
  have hpone : p.degree = 1 :=
    (Polynomial.degree_eq_iff_natDegree_eq hp.ne_zero).mpr (hdegree.symm.trans hfone)
  exact Polynomial.exists_root_of_degree_eq_one hpone

/-- Stacks Project, Tag 0BSP: the residue field at any nonzero prime of a
normal domain with separably closed fraction field is algebraically closed. -/
theorem isAlgClosed_primeResidueField_of_isSepClosed_fractionRing
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] [IsSepClosed K]
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
    IsAlgClosed p.ResidueField := by
  let S := Localization.AtPrime p
  let : Algebra S K := IsLocalization.localizationAlgebraOfSubmonoidLe
    S K p.primeCompl R⁰ p.primeCompl_le_nonZeroDivisors
  have : IsScalarTower R S K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      S K p.primeCompl R⁰ p.primeCompl_le_nonZeroDivisors
  have : IsFractionRing S K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl S K
  have : IsIntegrallyClosed S := isIntegrallyClosed_of_isLocalization
    S p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hm : IsLocalRing.maximalIdeal S ≠ ⊥ := by
    intro h
    apply hp
    apply bot_unique
    intro a ha
    have hmem : algebraMap R S a ∈ IsLocalRing.maximalIdeal S :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff S p a).mpr ha
    rw [h] at hmem
    have hzero : algebraMap R S a = algebraMap R S 0 :=
      (Ideal.mem_bot.mp hmem).trans (map_zero (algebraMap R S)).symm
    exact (IsLocalization.injective S p.primeCompl_le_nonZeroDivisors) hzero
  exact isAlgClosed_residueField_of_isSepClosed_fractionRing S K hm

end EtaleFundamentalGroups.StrictHenselian
