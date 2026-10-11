/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.AtPrime.Extension
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Nyll.SchemeTheory.LocalGeometry.HeightOne.Localization
import Nyll.EtaleFundamentalGroups.Normalization.Primes.Basic
import Nyll.SchemeTheory.Divisors.NormalCrossings.Basic

/-!
# Products of the actual ramification indices above a boundary branch

For a finite normalization, the product of the ramification indices of all
primes above one height-one branch is a common multiple of exactly the local
ramification indices which must be cancelled by the Abhyankar root cover.
Unlike a factorial of the total field degree, this product contains no
unramified residue-degree factors.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uR uS uA uK uL

@[reducible]
private noncomputable def finitePrimesOverFintype
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.QuasiFinite R S] (p : Ideal R) :
    Fintype (p.primesOver S) :=
  (Algebra.QuasiFinite.finite_primesOver p).fintype

/-- The product of the actual ramification indices of all primes of `S`
above `p`. -/
noncomputable def branchRamificationProduct
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.QuasiFinite R S] (p : Ideal R) : ℕ := by
  letI : Fintype (p.primesOver S) := finitePrimesOverFintype p
  exact ∏ q : p.primesOver S, q.1.ramificationIdx R

/-- Every actual ramification index above `p` divides the branch product. -/
theorem ramificationIdx_dvd_branchRamificationProduct
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.QuasiFinite R S]
    (p : Ideal R) (q : p.primesOver S) :
    q.1.ramificationIdx R ∣ branchRamificationProduct (S := S) p := by
  classical
  let : Fintype (p.primesOver S) := finitePrimesOverFintype p
  change q.1.ramificationIdx R ∣
    ∏ q' : p.primesOver S, q'.1.ramificationIdx R
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ q)

/-- For a finite extension, the branch ramification product is positive. -/
theorem branchRamificationProduct_pos
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S]
    (p : Ideal R) :
    0 < branchRamificationProduct (S := S) p := by
  classical
  let : Fintype (p.primesOver S) := finitePrimesOverFintype p
  change 0 < ∏ q : p.primesOver S, q.1.ramificationIdx R
  exact Finset.prod_pos fun q _ ↦ Ideal.ramificationIdx_pos q.1 R

/-- The branch product for a height-one prime of a regular model, computed
in the canonical DVR localization and its normalization in `L`. -/
noncomputable def normalizationBranchRamificationProduct
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) : ℕ := by
  let V := Localization.AtPrime p
  letI : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) p
  letI : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) p
  letI : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) p
  letI : IsFractionRing V K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) p
  letI : IsDiscreteValuationRing V :=
    isDiscreteValuationRing_localizationAtPrime_of_height_eq_one A p hp
  let C := integralClosure V L
  letI : Module.Finite V C :=
    IsIntegralClosure.finite V K L C
  exact branchRamificationProduct
    (S := C) (IsLocalRing.maximalIdeal V : Ideal V)

/-- The branch product is positive. -/
theorem normalizationBranchRamificationProduct_pos
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    0 < normalizationBranchRamificationProduct
      (K := K) (L := L) p hp := by
  let V := Localization.AtPrime p
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) p
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) p
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) p
  let : IsFractionRing V K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) p
  let : IsDiscreteValuationRing V :=
    isDiscreteValuationRing_localizationAtPrime_of_height_eq_one A p hp
  let C := integralClosure V L
  let : Module.Finite V C :=
    IsIntegralClosure.finite V K L C
  change 0 < branchRamificationProduct
    (S := C) (IsLocalRing.maximalIdeal V : Ideal V)
  exact branchRamificationProduct_pos
    (S := C) (IsLocalRing.maximalIdeal V)

/-- The ramification index of a chosen normalization prime divides the
branch product computed after localizing at its height-one contraction. -/
theorem normalizationPrime_ramificationIdx_dvd_branchRamificationProduct
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver p] :
    Q.ramificationIdx A ∣
      normalizationBranchRamificationProduct
        (K := K) (L := L) p hp := by
  let V := Localization.AtPrime p
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) p
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) p
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) p
  let : IsFractionRing V K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) p
  let : IsDiscreteValuationRing V :=
    isDiscreteValuationRing_localizationAtPrime_of_height_eq_one A p hp
  let C := integralClosure V L
  let : Module.Finite V C :=
    IsIntegralClosure.finite V K L C
  let q := localizedNormalizationPrime (K := K) (L := L) p Q
  let : q.IsMaximal :=
    localizedNormalizationPrime_isMaximal (K := K) (L := L) p Q
  let : q.IsPrime := inferInstance
  let : q.LiesOver (IsLocalRing.maximalIdeal V) :=
    localizedNormalizationPrime_liesOver (K := K) (L := L) p Q
  let qOver : (IsLocalRing.maximalIdeal V).primesOver C :=
    ⟨q, inferInstance, inferInstance⟩
  have hdiv :=
    ramificationIdx_dvd_branchRamificationProduct
      (S := C) (IsLocalRing.maximalIdeal V) qOver
  change q.ramificationIdx V ∣
    branchRamificationProduct
      (S := C) (IsLocalRing.maximalIdeal V) at hdiv
  rw [localizedNormalizationPrime_ramificationIdx
    (K := K) (L := L) p Q] at hdiv
  exact hdiv

/-- The branch product attached directly to a prime element. -/
noncomputable def normalizationPrimeElementRamificationProduct
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (t : A) (ht : Prime t) : ℕ := by
  letI : (Ideal.span {t}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime ht
  exact normalizationBranchRamificationProduct (K := K) (L := L)
    (Ideal.span {t})
      (Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr ht.ne_zero) ht.not_isUnit)

/-- A prime element's branch product is positive. -/
theorem normalizationPrimeElementRamificationProduct_pos
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (t : A) (ht : Prime t) :
    0 < normalizationPrimeElementRamificationProduct
      (K := K) (L := L) t ht := by
  let : (Ideal.span {t}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime ht
  exact normalizationBranchRamificationProduct_pos
    (K := K) (L := L) (Ideal.span {t})
      (Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr ht.ne_zero) ht.not_isUnit)

/-- A chosen normalization prime above a prime element has ramification
index dividing that element's branch product. -/
theorem normalizationPrime_ramificationIdx_dvd_primeElementProduct
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (t : A) (ht : Prime t)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {t})] :
    Q.ramificationIdx A ∣
      normalizationPrimeElementRamificationProduct
        (K := K) (L := L) t ht := by
  let : (Ideal.span {t}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime ht
  exact normalizationPrime_ramificationIdx_dvd_branchRamificationProduct
    (K := K) (L := L) (Ideal.span {t})
      (Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr ht.ne_zero) ht.not_isUnit) Q

/-- The actual ramification-product exponent on every labelled branch of a
split strict-normal-crossings chart; non-boundary parameters receive
exponent one. -/
noncomputable def splitStrictNormalCrossingsBranchRamificationProduct
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {d r : ℕ} {f : A} (t : Fin d → A)
    (hNC : IsSplitStrictNormalCrossingsAt f t r) (j : Fin d) : ℕ :=
  if hj : j.1 < r then
    normalizationPrimeElementRamificationProduct
      (K := K) (L := L) (t j) (hNC.2.2.2.1 j hj)
  else 1

/-- Every exponent in the strict-normal-crossings branch-product family is
positive. -/
theorem splitStrictNormalCrossingsBranchRamificationProduct_pos
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {d r : ℕ} {f : A} (t : Fin d → A)
    (hNC : IsSplitStrictNormalCrossingsAt f t r) (j : Fin d) :
    0 < splitStrictNormalCrossingsBranchRamificationProduct
      (K := K) (L := L) t hNC j := by
  classical
  by_cases hj : j.1 < r
  · simp only [splitStrictNormalCrossingsBranchRamificationProduct, hj,
      dite_true]
    exact normalizationPrimeElementRamificationProduct_pos
      (K := K) (L := L) (t j) (hNC.2.2.2.1 j hj)
  · simp [splitStrictNormalCrossingsBranchRamificationProduct, hj]

/-- On a labelled boundary branch, the chart exponent is the corresponding
normalization branch product. -/
theorem splitStrictNormalCrossingsBranchRamificationProduct_eq
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {d r : ℕ} {f : A} (t : Fin d → A)
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (j : Fin d) (hj : j.1 < r) :
    splitStrictNormalCrossingsBranchRamificationProduct
        (K := K) (L := L) t hNC j =
      normalizationPrimeElementRamificationProduct
        (K := K) (L := L) (t j) (hNC.2.2.2.1 j hj) := by
  simp [splitStrictNormalCrossingsBranchRamificationProduct, hj]

/-- A chosen normalization prime's ramification index divides its labelled
strict-normal-crossings branch exponent. -/
theorem normalizationPrime_ramificationIdx_dvd_splitStrictNormalCrossingsProduct
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {d r : ℕ} {f : A} (t : Fin d → A)
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (j : Fin d) (hj : j.1 < r)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {t j})] :
    Q.ramificationIdx A ∣
      splitStrictNormalCrossingsBranchRamificationProduct
        (K := K) (L := L) t hNC j := by
  rw [splitStrictNormalCrossingsBranchRamificationProduct_eq
    (K := K) (L := L) t hNC j hj]
  exact normalizationPrime_ramificationIdx_dvd_primeElementProduct
    (K := K) (L := L) (t j) (hNC.2.2.2.1 j hj) Q

end EtaleFundamentalGroups

end
