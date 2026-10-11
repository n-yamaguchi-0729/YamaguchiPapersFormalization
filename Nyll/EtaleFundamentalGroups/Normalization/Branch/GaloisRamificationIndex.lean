/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.NumberTheory.RamificationInertia.Galois
import Nyll.EtaleFundamentalGroups.Normalization.Branch.RamificationProduct

/-!
# The common branch ramification index in a Galois normalization

For a finite Galois extension, all normalization primes above one
height-one branch have the same ramification index.  This is the exponent
needed by the root cover: unlike the product of all branch indices, it does
not introduce a residual radical after selecting one actual branch factor.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

/-- The common ramification index above a height-one prime, computed in its
canonical DVR localization. -/
noncomputable def normalizationGaloisBranchRamificationIndex
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : Ideal A) [p.IsPrime] : ℕ := by
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
  let S := integralClosure V L
  exact (IsLocalRing.maximalIdeal V).ramificationIdxIn S

private theorem ramificationIdxIn_eq_localPrime
    {V : Type uA} {K : Type uK} {L : Type uL}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Field L]
    [Algebra V K] [IsFractionRing V K]
    [Algebra K L] [Algebra V L] [IsScalarTower V K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q : (IsLocalRing.maximalIdeal V).primesOver (integralClosure V L)) :
    (IsLocalRing.maximalIdeal V).ramificationIdxIn (integralClosure V L) =
      q.1.ramificationIdx V := by
  let S := integralClosure V L
  let : Module.Finite V S := IsIntegralClosure.finite V K L S
  let : IsFractionRing S L :=
    IsIntegralClosure.isFractionRing_of_finite_extension V K L S
  let : MulSemiringAction Gal(L/K) S :=
    IsIntegralClosure.MulSemiringAction V K L S
  let : IsGaloisGroup Gal(L/K) V S :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) V S K L
  change (IsLocalRing.maximalIdeal V).ramificationIdxIn S =
    q.1.ramificationIdx V
  exact Ideal.ramificationIdxIn_eq_ramificationIdx
    (IsLocalRing.maximalIdeal V) q.1 Gal(L/K)

/-- Every local normalization prime above the branch has the common Galois
ramification index. -/
theorem localNormalizationPrime_ramificationIdx_eq_galoisBranchIndex
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    let V := Localization.AtPrime p
    letI : Algebra V K :=
      localizationAtPrimeToFractionFieldAlgebra (K := K) p
    letI : Algebra V L :=
      localizationAtPrimeToExtensionAlgebra (K := K) (L := L) p
    letI : IsScalarTower V K L :=
      localizationAtPrimeToFractionFieldToExtension_isScalarTower
        (K := K) (L := L) p
    let S := integralClosure V L
    ∀ q : (IsLocalRing.maximalIdeal V).primesOver S,
      q.1.ramificationIdx V =
        normalizationGaloisBranchRamificationIndex
          (K := K) (L := L) p := by
  dsimp only
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
  intro q
  exact (ramificationIdxIn_eq_localPrime
    (V := V) (K := K) (L := L) q).symm

/-- The common Galois branch index is positive. -/
theorem normalizationGaloisBranchRamificationIndex_pos
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    0 < normalizationGaloisBranchRamificationIndex
      (K := K) (L := L) p := by
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
  let S := integralClosure V L
  let : Module.Finite V S := IsIntegralClosure.finite V K L S
  let : IsFractionRing S L :=
    IsIntegralClosure.isFractionRing_of_finite_extension V K L S
  let : MulSemiringAction Gal(L/K) S :=
    IsIntegralClosure.MulSemiringAction V K L S
  let : IsGaloisGroup Gal(L/K) V S :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) V S K L
  let : FaithfulSMul V S :=
    (faithfulSMul_iff_algebraMap_injective V S).mpr fun x y hxy ↦ by
      apply IsFractionRing.injective V K
      apply (algebraMap K L).injective
      have hco : algebraMap V L x = algebraMap V L y := by
        change (algebraMap V S x : L) = (algebraMap V S y : L)
        exact congrArg (fun z : S ↦ (z : L)) hxy
      simpa only [IsScalarTower.algebraMap_apply V K L] using hco
  change 0 < (IsLocalRing.maximalIdeal V).ramificationIdxIn S
  exact Nat.pos_of_ne_zero
    (Ideal.ramificationIdxIn_ne_zero Gal(L/K))

/-- A chosen prime of the original normalization has exactly the common
Galois branch ramification index. -/
theorem normalizationPrime_ramificationIdx_eq_galoisBranchIndex
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver p] :
    Q.ramificationIdx A =
      normalizationGaloisBranchRamificationIndex
        (K := K) (L := L) p := by
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
  let S := integralClosure V L
  let : Module.Finite V S := IsIntegralClosure.finite V K L S
  let q := localizedNormalizationPrime (K := K) (L := L) p Q
  let : q.IsMaximal :=
    localizedNormalizationPrime_isMaximal (K := K) (L := L) p Q
  let : q.IsPrime := inferInstance
  let : q.LiesOver (IsLocalRing.maximalIdeal V) :=
    localizedNormalizationPrime_liesOver (K := K) (L := L) p Q
  let qOver : (IsLocalRing.maximalIdeal V).primesOver S :=
    ⟨q, inferInstance, inferInstance⟩
  rw [← localizedNormalizationPrime_ramificationIdx
    (K := K) (L := L) p Q]
  exact localNormalizationPrime_ramificationIdx_eq_galoisBranchIndex
    (K := K) (L := L) p hp qOver

/-- The common Galois ramification index attached to a prime element. -/
noncomputable def normalizationPrimeElementGaloisRamificationIndex
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (t : A) (ht : Prime t) : ℕ := by
  letI : (Ideal.span {t}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime ht
  exact normalizationGaloisBranchRamificationIndex
    (K := K) (L := L) (Ideal.span {t})

/-- A prime element's common Galois branch index is positive. -/
theorem normalizationPrimeElementGaloisRamificationIndex_pos
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (t : A) (ht : Prime t) :
    0 < normalizationPrimeElementGaloisRamificationIndex
      (K := K) (L := L) t ht := by
  let : (Ideal.span {t}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime ht
  exact normalizationGaloisBranchRamificationIndex_pos
    (K := K) (L := L) (Ideal.span {t})
      (Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr ht.ne_zero) ht.not_isUnit)

/-- A chosen normalization prime over a prime element has exactly that
element's common Galois branch index. -/
theorem normalizationPrime_ramificationIdx_eq_primeElementGaloisIndex
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (t : A) (ht : Prime t)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {t})] :
    Q.ramificationIdx A =
      normalizationPrimeElementGaloisRamificationIndex
        (K := K) (L := L) t ht := by
  let : (Ideal.span {t}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime ht
  exact normalizationPrime_ramificationIdx_eq_galoisBranchIndex
    (K := K) (L := L) (Ideal.span {t})
      (Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr ht.ne_zero) ht.not_isUnit) Q

/-- The actual common Galois exponent on every labelled branch of a split
strict-normal-crossings chart; non-boundary parameters receive exponent
one. -/
noncomputable def splitStrictNormalCrossingsGaloisRamificationIndex
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {d r : ℕ} {f : A} (t : Fin d → A)
    (hNC : IsSplitStrictNormalCrossingsAt f t r) (j : Fin d) : ℕ :=
  if hj : j.1 < r then
    normalizationPrimeElementGaloisRamificationIndex
      (K := K) (L := L) (t j) (hNC.2.2.2.1 j hj)
  else 1

/-- Every strict-normal-crossings Galois branch exponent is positive. -/
theorem splitStrictNormalCrossingsGaloisRamificationIndex_pos
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {d r : ℕ} {f : A} (t : Fin d → A)
    (hNC : IsSplitStrictNormalCrossingsAt f t r) (j : Fin d) :
    0 < splitStrictNormalCrossingsGaloisRamificationIndex
      (K := K) (L := L) t hNC j := by
  classical
  by_cases hj : j.1 < r
  · simp only [splitStrictNormalCrossingsGaloisRamificationIndex, hj,
      dite_true]
    exact normalizationPrimeElementGaloisRamificationIndex_pos
      (K := K) (L := L) (t j) (hNC.2.2.2.1 j hj)
  · simp [splitStrictNormalCrossingsGaloisRamificationIndex, hj]

/-- On a labelled boundary branch, the chart exponent is the common
Galois ramification index. -/
theorem splitStrictNormalCrossingsGaloisRamificationIndex_eq
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {d r : ℕ} {f : A} (t : Fin d → A)
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (j : Fin d) (hj : j.1 < r) :
    splitStrictNormalCrossingsGaloisRamificationIndex
        (K := K) (L := L) t hNC j =
      normalizationPrimeElementGaloisRamificationIndex
        (K := K) (L := L) (t j) (hNC.2.2.2.1 j hj) := by
  simp [splitStrictNormalCrossingsGaloisRamificationIndex, hj]

/-- A chosen normalization prime over a labelled boundary branch has exactly
the exponent used by the Galois strict-normal-crossings root cover. -/
theorem
    normalizationPrime_ramificationIdx_eq_splitStrictNormalCrossingsGaloisIndex
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {d r : ℕ} {f : A} (t : Fin d → A)
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (j : Fin d) (hj : j.1 < r)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span ({t j} : Set A))] :
    Q.ramificationIdx A =
      splitStrictNormalCrossingsGaloisRamificationIndex
        (K := K) (L := L) t hNC j := by
  rw [splitStrictNormalCrossingsGaloisRamificationIndex_eq
    (K := K) (L := L) t hNC j hj]
  exact normalizationPrime_ramificationIdx_eq_primeElementGaloisIndex
    (K := K) (L := L) (t j) (hNC.2.2.2.1 j hj) Q

end EtaleFundamentalGroups

end
