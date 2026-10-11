/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Uniformizer radicals force divisibility of the ramification index

The length definition of the ramification index and additivity of order of
vanishing give the divisibility used in Stacks Project, Tag 0BUB. The root
need not be a uniformizer, and no residue separability or characteristic-zero
hypothesis is used.

Reference: https://stacks.math.columbia.edu/tag/0BUB
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- The actual coefficient map to the prime localization, constructed as a
ring-homomorphism composite. It does not install another scalar action. -/
private def localizedCoefficient
    (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (q : Ideal B) [q.IsPrime] : A →+* Localization.AtPrime q :=
  (algebraMap B (Localization.AtPrime q)).comp (algebraMap A B)

/-- The prime generator computes the literal ramification length. All
localization scalar structures needed by that length stay in this owner. -/
private theorem ramificationIdx_eq_ord_localizedCoefficient
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (q : Ideal B) [q.IsPrime] (π : A)
    (hunder : q.under A = Ideal.span (Set.singleton π)) :
    q.ramificationIdx A =
      (Ring.ord (Localization.AtPrime q) (localizedCoefficient A q π)).toNat := by
  rw [Ideal.ramificationIdx_def, hunder, Ideal.map_span]
  have himage : (algebraMap A (Localization.AtPrime q)) '' Set.singleton π =
      Set.singleton (algebraMap A (Localization.AtPrime q) π) := Set.image_singleton
  rw [himage]
  rfl

/-- An original DVR uniformizer computes the actual ramification index
through the literal composite coefficient map into the prime localization.
The A-action on that localization stays inside the existing length owner. -/
theorem ramificationIdx_eq_ord_localized_uniformizer
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsDomain A] [IsDiscreteValuationRing A] [Algebra A B]
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal A)]
    (π : A) (hπ : Irreducible π) :
    Q.ramificationIdx A =
      (Ring.ord (Localization.AtPrime Q)
        (algebraMap B (Localization.AtPrime Q) (algebraMap A B π))).toNat := by
  exact ramificationIdx_eq_ord_localizedCoefficient Q π
    ((Q.over_def (IsLocalRing.maximalIdeal A)).symm.trans
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ))

/-- The actual order-of-vanishing calculation is a one-ring statement. -/
private theorem exponent_dvd_ord_of_pow_eq
    {S : Type u} [CommRing S] (n : ℕ) (α β : S)
    (hα : α ∈ nonZeroDivisors S) (hpow : α ^ n = β) :
    n ∣ (Ring.ord S β).toNat := by
  rw [← hpow, Ring.ord_pow hα, nsmul_eq_mul, ENat.toNat_mul, ENat.toNat_natCast]
  exact dvd_mul_right n (Ring.ord S α).toNat

/-- An actual radical of a generator of the contracted prime forces its
exponent to divide the ramification index. -/
theorem exponent_dvd_ramificationIdx_of_pow_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    (q : Ideal B) [q.IsPrime] (π : A) (hπ : π ≠ 0)
    (hunder : q.under A = Ideal.span (Set.singleton π))
    (n : ℕ) (hn : n ≠ 0) (α : B)
    (hα : α ^ n = algebraMap A B π) :
    n ∣ q.ramificationIdx A := by
  have hαzero : α ≠ 0 := by
    intro hz
    have hπzero : algebraMap A B π = 0 := by
      rw [← hα, hz, zero_pow hn]
    exact hπ ((FaithfulSMul.algebraMap_injective A B)
      (hπzero.trans (map_zero (algebraMap A B)).symm))
  rw [ramificationIdx_eq_ord_localizedCoefficient q π hunder]
  apply exponent_dvd_ord_of_pow_eq n
    (algebraMap B (Localization.AtPrime q) α) (localizedCoefficient A q π)
  · exact IsLocalization.nonZeroDivisors_le_comap q.primeCompl (Localization.AtPrime q)
      (mem_nonZeroDivisors_iff_ne_zero.mpr hαzero)
  · rw [← map_pow, hα]
    rfl

/-- The original DVR specialization, for every prime over the maximal
ideal, without imposing separability on its residue extension. -/
theorem exponent_dvd_ramificationIdx_of_uniformizer_pow_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A]
    [Algebra A B] [FaithfulSMul A B]
    (q : Ideal B) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal A)]
    (π : A) (hπ : Irreducible π) (n : ℕ) (hn : n ≠ 0)
    (α : B) (hα : α ^ n = algebraMap A B π) :
    n ∣ q.ramificationIdx A := by
  apply exponent_dvd_ramificationIdx_of_pow_eq q π hπ.ne_zero
    ((q.over_def (IsLocalRing.maximalIdeal A)).symm.trans
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ)) n hn α hα

end EtaleFundamentalGroups.Inertia

end
