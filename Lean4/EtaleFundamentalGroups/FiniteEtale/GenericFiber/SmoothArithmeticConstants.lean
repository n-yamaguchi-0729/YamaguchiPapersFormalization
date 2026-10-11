/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.RingTheory.SmoothReduced
import Mathlib.Data.Int.Order.Units
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.LocalRing.ResidueField.Separable
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Smooth arithmetic schemes and fields of constants

A number field admitting a faithfully flat algebra which is smooth over the
integers is unramified at every finite prime. Smoothness gives reduced
special fibers; faithful flatness descends this reducedness to the ring of
integers. The local unramified criterion and Minkowski then force degree one.
-/

noncomputable section

open scoped TensorProduct NumberField

namespace EtaleFundamentalGroups

private theorem unramifiedAt_of_radical_specialFiber
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (p : Ideal R) [p.IsMaximal]
    [PerfectField p.ResidueField] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hred : (p.map (algebraMap R S)).IsRadical) :
    Algebra.IsUnramifiedAt R q := by
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  apply (Algebra.isUnramifiedAt_iff_map_eq R p q).mpr
  refine ⟨inferInstance, ?_⟩
  let : Field (R ⧸ p) := Ideal.Quotient.field p
  have : Module.Finite (R ⧸ p) (S ⧸ p.map (algebraMap R S)) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ p) _
  have : IsArtinianRing (S ⧸ p.map (algebraMap R S)) :=
    IsArtinianRing.of_finite (R ⧸ p) _
  have hle : p.map (algebraMap R S) ≤ q :=
    Ideal.map_le_iff_le_comap.mpr (q.over_def p).le
  have hmin : q ∈ (p.map (algebraMap R S)).minimalPrimes := by
    have : (q.map (Ideal.Quotient.mk (p.map (algebraMap R S)))).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hle)
    rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨q.map (Ideal.Quotient.mk (p.map (algebraMap R S))),
      IsArtinianRing.mem_minimalPrimes bot_le, Ideal.comap_map_mk hle⟩
  calc
    p.map (algebraMap R (Localization.AtPrime q)) =
        (p.map (algebraMap R S)).map (algebraMap S (Localization.AtPrime q)) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S (Localization.AtPrime q)]
    _ = (p.map (algebraMap R S)).radical.map
        (algebraMap S (Localization.AtPrime q)) := by rw [hred.radical]
    _ = ((p.map (algebraMap R S)).map
        (algebraMap S (Localization.AtPrime q))).radical :=
      IsLocalization.map_radical q.primeCompl (Localization.AtPrime q) _
    _ = q.map (algebraMap S (Localization.AtPrime q)) :=
      IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime q) q
        (p.map (algebraMap R S)) hmin
    _ = IsLocalRing.maximalIdeal (Localization.AtPrime q) :=
      Localization.AtPrime.map_eq_maximalIdeal

/-- Smoothness over the integers and faithful flatness over the ring of
integers force every finite prime of that ring of integers to be unramified. -/
theorem ringOfIntegers_unramifiedAt_of_smooth_faithfullyFlat
    (K A : Type) [Field K] [NumberField K] [CommRing A]
    [Algebra (𝓞 K) A] [Module.FaithfullyFlat (𝓞 K) A] [Algebra.Smooth ℤ A]
    (p : Ideal ℤ) [p.IsMaximal]
    (q : Ideal (𝓞 K)) [q.IsPrime] [q.LiesOver p] :
    Algebra.IsUnramifiedAt ℤ q := by
  let : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  have : IsReduced ((ℤ ⧸ p) ⊗[ℤ] A) :=
    Algebra.Smooth.isReduced_of_field (K := ℤ ⧸ p)
  have hredA : (p.map (algebraMap ℤ A)).IsRadical := by
    apply (Ideal.isRadical_iff_quotient_reduced _).mpr
    exact isReduced_of_injective
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A p)
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A p).injective
  have hredK : (p.map (algebraMap ℤ (𝓞 K))).IsRadical := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat
      (B := A) (p.map (algebraMap ℤ (𝓞 K)))]
    apply Ideal.IsRadical.comap
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact hredA
  exact unramifiedAt_of_radical_specialFiber p q hredK

/-- A number field with a faithfully flat algebra smooth over `ℤ` is `ℚ`
in degree. In the geometric application the algebra comes from a finite
affine cover of the smooth arithmetic covering scheme. -/
theorem numberField_finrank_eq_one_of_smooth_faithfullyFlat_ringOfIntegers
    (K A : Type) [Field K] [NumberField K] [CommRing A]
    [Algebra (𝓞 K) A] [Module.FaithfullyFlat (𝓞 K) A] [Algebra.Smooth ℤ A] :
    Module.finrank ℚ K = 1 := by
  have hunit : IsUnit (NumberField.discr K) := by
    by_contra hnunit
    obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor
      hnunit (NumberField.discr_ne_zero K)
    apply ((NumberField.not_dvd_discr_iff_forall_liesOver K (𝓞 K)
      (irreducible_iff_prime.mp hp)).mpr ?_) hpd
    intro q hq hqp
    have : q.IsMaximal := hq
    have : q.LiesOver (Ideal.span {p}) := hqp
    have hprime : Prime p := irreducible_iff_prime.mp hp
    have hspan : Ideal.span {p} ≠ (⊥ : Ideal ℤ) :=
      Ideal.span_singleton_eq_bot.not.mpr hprime.ne_zero
    have : (Ideal.span {p}).IsPrime :=
      (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
    have : (Ideal.span {p}).IsMaximal :=
      Ring.HasFiniteQuotients.maximalOfPrime hspan
    exact ringOfIntegers_unramifiedAt_of_smooth_faithfullyFlat K A
      (Ideal.span {p}) q
  have habs : |NumberField.discr K| = 1 := Int.isUnit_iff_abs_eq.mp hunit
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  by_contra hne
  have hgt : 1 < Module.finrank ℚ K := by omega
  have hbound := NumberField.abs_discr_gt_two (K := K) hgt
  omega

end EtaleFundamentalGroups
