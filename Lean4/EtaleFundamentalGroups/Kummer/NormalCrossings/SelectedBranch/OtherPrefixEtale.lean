/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import SchemeTheory.RingTheory.Ramification.Etale.BaseChange
import EtaleFundamentalGroups.Kummer.AdjoinRoot.FormallyEtale
import EtaleFundamentalGroups.Kummer.IteratedRadical.BaseChange
import EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.BranchAtLargerPrime
import EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.GaloisFullRootCover
import EtaleFundamentalGroups.Purity.SpecialLocal.DimensionTwoIntegralClosure

/-!
# The other-root prefix at a selected Galois branch

After passing to the DVR of the selected branch, all other regular
parameters are units.  Characteristic zero of the selected branch residue
field makes every positive Galois root exponent a unit as well.  Consequently
the base-changed other-root prefix is finite etale.

The final theorem in this leaf chooses a prime after tensoring any faithfully
flat etale base change with a given algebra.  Its explicit contraction along
the right tensor factor is precisely the input to the ramification-index
comparison theorem.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open RingTheory.Sequence

universe u uA uK uL

private theorem prime_algebraMap_localizationAtPrime_of_mem
    {A : Type u} [CommRing A] [IsDomain A]
    (P : Ideal A) [P.IsPrime] {t : A} (ht : Prime t) (htP : t ∈ P) :
    Prime (algebraMap A (Localization.AtPrime P) t) := by
  rcases prime_or_isUnit_algebraMap_localizationAtPrime P ht with
    hprime | hunit
  · exact hprime
  · have htCompl : t ∈ P.primeCompl :=
      (IsLocalization.AtPrime.isUnit_to_map_iff
        (Localization.AtPrime P) P t).mp hunit
    exact (htCompl htP).elim

/-- Iterated Kummer radicals with positive unit exponents and unit
radicands are etale over their base. -/
theorem iteratedRadical_etale_of_exponents_radicands_isUnit
    {A : Type u} [CommRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hnUnit : ∀ i, IsUnit (n i : A))
    (haUnit : ∀ i, IsUnit (a i)) :
    Algebra.Etale A (iteratedRadical A r n a) := by
  induction r with
  | zero =>
      change Algebra.Etale A A
      infer_instance
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      have hPrefix : Algebra.Etale A T :=
        ih (Fin.init n) (Fin.init a)
          (fun i ↦ hn i.castSucc)
          (fun i ↦ hnUnit i.castSucc)
          (fun i ↦ haUnit i.castSucc)
      let : Algebra.Etale A T := hPrefix
      have hnLast : IsUnit (n (Fin.last r) : T) := by
        simpa using
          (hnUnit (Fin.last r)).map (algebraMap A T)
      have haLast :
          IsUnit (algebraMap A T (a (Fin.last r))) :=
        (haUnit (Fin.last r)).map (algebraMap A T)
      have hFormal : Algebra.FormallyEtale T (AdjoinRoot f) := by
        exact formallyEtale_adjoinRoot_X_pow_sub_C
          (hn (Fin.last r)) hnLast haLast
      let : Algebra.Etale T (AdjoinRoot f) :=
        { formallyEtale := hFormal
          finitePresentation := inferInstance }
      change Algebra.Etale A (AdjoinRoot f)
      exact Algebra.Etale.comp A T (AdjoinRoot f)

/-- Every parameter other than the selected one becomes a unit in the
selected branch DVR.  If it is outside the height-two prime it is already a
unit after the first localization.  If it lies in that prime, the two
distinct parameters form a regular pair, so the other parameter is not in
the selected height-one prime. -/
theorem heightTwoConditionalOtherRadicand_isUnit_at_selectedBranch
    {A : Type uA} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsRegularRing A]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P) (sigma : Equiv.Perm (Fin d)) :
    let R := Localization.AtPrime P
    let y : R := algebraMap A R (t i)
    let hy : Prime y :=
      prime_algebraMap_localizationAtPrime_of_mem P
        (hNC.2.2.2.1 i hi) htiP
    let pR := Ideal.span ({y} : Set R)
    letI : pR.IsPrime := Ideal.isPrime_span_singleton_of_prime hy
    let V := Localization.AtPrime pR
    ∀ k,
      IsUnit (algebraMap R V
        (heightTwoConditionalOtherRadicand t i P sigma k)) := by
  dsimp only
  let R := Localization.AtPrime P
  let y : R := algebraMap A R (t i)
  have hy : Prime y :=
    prime_algebraMap_localizationAtPrime_of_mem P
      (hNC.2.2.2.1 i hi) htiP
  let pR := Ideal.span ({y} : Set R)
  let : pR.IsPrime := Ideal.isPrime_span_singleton_of_prime hy
  let V := Localization.AtPrime pR
  intro k
  let j : Fin (d + 1) := i.succAbove (sigma k)
  let aR : R := heightTwoConditionalOtherRadicand t i P sigma k
  by_cases htjP : t j ∈ P
  · have hij : i ≠ j := (Fin.succAbove_ne i (sigma k)).symm
    have hregular : IsRegular R [y, aR] := by
      simpa only [R, y, aR, j,
        heightTwoConditionalOtherRadicand] using
        (regular_pair_localizationAtPrime_of_two_splitStrictNormalCrossingsParameters
          hNC i j hij P hP htiP htjP).1
    have hrel : IsRelPrime y aR :=
      (SpecialLocalPurity.regular_pair_nonzero_and_isRelPrime
        hregular).2.2
    have hyMem : y ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff R P (t i)).mpr htiP
    have haNot : aR ∉ pR := by
      intro ha
      have hyDvd : y ∣ aR := Ideal.mem_span_singleton.mp ha
      have hyUnit : IsUnit y := hrel.isUnit_of_dvd hyDvd
      exact ((IsLocalRing.notMem_maximalIdeal).mpr hyUnit) hyMem
    exact
      (IsLocalization.AtPrime.isUnit_to_map_iff V pR aR).mpr haNot
  · have haRUnit : IsUnit aR := by
      change IsUnit (algebraMap A R (t j))
      exact
        (IsLocalization.AtPrime.isUnit_to_map_iff R P (t j)).mpr htjP
    exact haRUnit.map (algebraMap R V)

/-- Characteristic zero of the selected branch residue field makes every
positive conditional Galois exponent a unit in the selected branch DVR. -/
theorem heightTwoConditionalOtherExponent_isUnit_at_selectedBranch
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (htiP : t i ∈ P)
    (hCharZero : CharZero (A ⧸ Ideal.span ({t i} : Set A)))
    (sigma : Equiv.Perm (Fin d)) :
    let e := heightTwoOtherBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    let n := heightTwoConditionalOtherExponent t i r P e sigma
    let R := Localization.AtPrime P
    let y : R := algebraMap A R (t i)
    let hy : Prime y :=
      prime_algebraMap_localizationAtPrime_of_mem P
        (hNC.2.2.2.1 i hi) htiP
    let pR := Ideal.span ({y} : Set R)
    letI : pR.IsPrime := Ideal.isPrime_span_singleton_of_prime hy
    let V := Localization.AtPrime pR
    ∀ k, IsUnit (n k : V) := by
  dsimp only
  let e := heightTwoOtherBranchGaloisRamificationIndex
    (K := K) (L := L) t hNC i
  let n := heightTwoConditionalOtherExponent t i r P e sigma
  let R := Localization.AtPrime P
  let y : R := algebraMap A R (t i)
  have hy : Prime y :=
    prime_algebraMap_localizationAtPrime_of_mem P
      (hNC.2.2.2.1 i hi) htiP
  let pR := Ideal.span ({y} : Set R)
  let : pR.IsPrime := Ideal.isPrime_span_singleton_of_prime hy
  let V := Localization.AtPrime pR
  let : CharZero (V ⧸ IsLocalRing.maximalIdeal V) := by
    simpa only [R, y, pR, V] using
      (charZero_twiceLocalized_splitStrictNormalCrossingsBranchResidue
        hNC i hi P htiP hCharZero)
  have hn : ∀ k, 0 < n k := by
    intro k
    by_cases hk : (i.succAbove (sigma k)).1 < r ∧
        t (i.succAbove (sigma k)) ∈ P
    · simpa [n, e, heightTwoConditionalOtherExponent, hk] using
        (heightTwoOtherBranchGaloisRamificationIndex_pos
          (K := K) (L := L) t hNC i (sigma k))
    · simp [n, heightTwoConditionalOtherExponent, hk]
  intro k
  apply (IsLocalRing.residue_ne_zero_iff_isUnit (n k : V)).mp
  change ((n k : ℕ) :
    (V ⧸ IsLocalRing.maximalIdeal V)) ≠ 0
  exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hn k))

/-- The canonical base change of the other-root prefix to the selected
branch DVR is finite, faithfully flat, and etale.  All unit conditions are
produced from strict-normal-crossings geometry and characteristic zero of the
selected branch residue field. -/
theorem heightTwoGaloisOtherRootPrefix_finiteEtale_at_selectedBranch
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P)
    (hCharZero : CharZero (A ⧸ Ideal.span ({t i} : Set A)))
    (sigma : Equiv.Perm (Fin d)) :
    let e := heightTwoOtherBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    let n := heightTwoConditionalOtherExponent t i r P e sigma
    let R := Localization.AtPrime P
    letI : Algebra R K :=
      localizationAtPrimeToFractionFieldAlgebra (K := K) P
    letI : Algebra R L :=
      localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI : IsScalarTower R K L :=
      localizationAtPrimeToFractionFieldToExtension_isScalarTower
        (K := K) (L := L) P
    letI : IsFractionRing R K :=
      localizationAtPrimeToFractionField_isFractionRing (K := K) P
    let aR : Fin d → R :=
      heightTwoConditionalOtherRadicand t i P sigma
    let y : R := algebraMap A R (t i)
    let hy : Prime y :=
      prime_algebraMap_localizationAtPrime_of_mem P
        (hNC.2.2.2.1 i hi) htiP
    let pR := Ideal.span ({y} : Set R)
    letI : pR.IsPrime := Ideal.isPrime_span_singleton_of_prime hy
    let V := Localization.AtPrime pR
    let aV : Fin d → V := fun k ↦ algebraMap R V (aR k)
    let E := iteratedRadical V d n aV
    Module.Finite V E ∧
      Module.FaithfullyFlat V E ∧ Algebra.Etale V E := by
  dsimp only
  let e := heightTwoOtherBranchGaloisRamificationIndex
    (K := K) (L := L) t hNC i
  let n := heightTwoConditionalOtherExponent t i r P e sigma
  let R := Localization.AtPrime P
  let : Algebra R K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra R L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower R K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  let : IsFractionRing R K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) P
  let aR : Fin d → R :=
    heightTwoConditionalOtherRadicand t i P sigma
  let y : R := algebraMap A R (t i)
  have hy : Prime y :=
    prime_algebraMap_localizationAtPrime_of_mem P
      (hNC.2.2.2.1 i hi) htiP
  let pR := Ideal.span ({y} : Set R)
  let : pR.IsPrime := Ideal.isPrime_span_singleton_of_prime hy
  let V := Localization.AtPrime pR
  let aV : Fin d → V := fun k ↦ algebraMap R V (aR k)
  let E := iteratedRadical V d n aV
  have hn : ∀ k, 0 < n k := by
    intro k
    by_cases hk : (i.succAbove (sigma k)).1 < r ∧
        t (i.succAbove (sigma k)) ∈ P
    · simpa [n, e, heightTwoConditionalOtherExponent, hk] using
        (heightTwoOtherBranchGaloisRamificationIndex_pos
          (K := K) (L := L) t hNC i (sigma k))
    · simp [n, heightTwoConditionalOtherExponent, hk]
  have hnUnit : ∀ k, IsUnit (n k : V) := by
    simpa only [e, n, R, y, pR, V] using
      (heightTwoConditionalOtherExponent_isUnit_at_selectedBranch
        (K := K) (L := L) hNC i hi P htiP hCharZero sigma)
  have haUnit : ∀ k, IsUnit (aV k) := by
    simpa only [R, aR, y, pR, V, aV] using
      (heightTwoConditionalOtherRadicand_isUnit_at_selectedBranch
        hNC i hi P hP htiP sigma)
  have hFinite : Module.Finite V E :=
    finite_iteratedRadical n aV hn
  have hFaithful : Module.FaithfullyFlat V E :=
    faithfullyFlat_iteratedRadical n aV hn
  have hEtale : Algebra.Etale V E :=
    iteratedRadical_etale_of_exponents_radicands_isUnit
      n aV hn hnUnit haUnit
  exact ⟨hFinite, hFaithful, hEtale⟩

/-- A prime survives tensoring on the left by a faithfully flat etale
algebra.  The chosen prime has explicit contraction along `includeRight`, and
its ramification index is unchanged. -/
theorem exists_tensorProduct_prime_over_right_ramificationIdx_eq_of_etale
    {R B E : Type*} [CommRing R] [CommRing B] [CommRing E]
    [Algebra R B] [Algebra R E]
    [Algebra.Etale R E] [Module.FaithfullyFlat R E]
    (q : Ideal B) [q.IsPrime] :
    ∃ Q : Ideal (E ⊗[R] B),
      Q.IsPrime ∧
        Q.comap Algebra.TensorProduct.includeRight.toRingHom = q ∧
          Q.ramificationIdx E = q.ramificationIdx R := by
  let T := E ⊗[R] B
  let T' := B ⊗[R] E
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra B T' := Algebra.TensorProduct.leftAlgebra
  let : Module.FaithfullyFlat B T' := inferInstance
  let e : T' ≃ₐ[B] T :=
    { toRingEquiv := (Algebra.TensorProduct.comm R B E).toRingEquiv
      commutes' := by
        intro b
        rfl }
  let : Module.FaithfullyFlat B T :=
    Module.FaithfullyFlat.of_linearEquiv B T' e.symm.toLinearEquiv
  obtain ⟨Q, hQPrime, hQOver⟩ :=
    Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := T) q
  let : Q.IsPrime := hQPrime
  have hQ :
      Q.comap Algebra.TensorProduct.includeRight.toRingHom = q := by
    change Q.comap (algebraMap B T) = q
    exact hQOver.over.symm
  refine ⟨Q, hQPrime, hQ, ?_⟩
  exact ramificationIdx_tensorProduct_eq_of_etale q Q hQ

end EtaleFundamentalGroups.Kummer

end
