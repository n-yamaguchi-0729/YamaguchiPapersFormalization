/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.IteratedRadical.ExponentUnit.LastPrimeOrUnit
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.PrimeParameterLocalization
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.FullRootCover.FixedComponentPurity

/-!
# The selected full-cover exponent is a boundary unit

Purity for every fixed generic tensor component supplies global etaleness of
its normalization over the exact height-two full root cover.  The localized
strict-normal-crossings parameters supply the prime-or-unit boundary data.
Thus the last-exponent obstruction leaves only primitive composite
boundary-away etaleness as an additional map-shaped input.
-/

noncomputable section

open Polynomial
open scoped BigOperators TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uA uK uL

/-- For the exact Galois full root cover at a height-two point, purity of each
fixed tensor component and primitive composite boundary-away etaleness force
the selected-branch ramification exponent to be a unit in the localized
base.  The permutation, cover geometry, purity, and localized
prime-or-unit/characteristic-zero boundary data are produced internally. -/
theorem
    splitStrictNormalCrossings_heightTwo_galoisFullRootCover_fixedComponent_selectedExponent_isUnit
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Module.Finite A (integralClosure A L)]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P)
    (hCharZero : ∀ j, j.1 < r →
      CharZero (A ⧸ Ideal.span ({t j} : Set A)))
    (hAwayBase : (Localization.awayMap
      (algebraMap A (integralClosure A L)) f).Etale) :
    let e := heightTwoOtherBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    let N := heightTwoSelectedBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    ∃ σ : Equiv.Perm (Fin d),
      let R := Localization.AtPrime P
      let n := heightTwoConditionalOtherExponent t i r P e σ
      let a : Fin d → R := heightTwoConditionalOtherRadicand t i P σ
      let B := iteratedRadical R d n a
      let y : R := algebraMap A R (t i)
      let F : B[X] := X ^ N - C (algebraMap R B y)
      let D := AdjoinRoot F
      ∃ hdomainD : IsDomain D,
      let : IsDomain D := hdomainD
      let K' := FractionRing D
      let : Algebra R K :=
        localizationAtPrimeToFractionFieldAlgebra (K := K) P
      let : IsFractionRing R K :=
        localizationAtPrimeToFractionField_isFractionRing (K := K) P
      let : Algebra K K' :=
        galoisFullRootCoverFractionFieldAlgebra n a
          (heightTwoConditionalOtherExponent_pos_of_pos t i r P e
            (heightTwoOtherBranchGaloisRamificationIndex_pos
              (K := K) (L := L) t hNC i) σ)
          N
          (heightTwoSelectedBranchGaloisRamificationIndex_pos
            (K := K) (L := L) t hNC i) y
      ∀ (m : Ideal (K' ⊗[K] L)) (hm : m.IsMaximal),
        let : m.IsMaximal := hm
        let M := GenericTensorFieldComponent m
        let : Algebra D M :=
          genericTensorFieldComponentLeftScalarAlgebra (R := D) m
        let : SMul D M :=
          (genericTensorFieldComponentLeftScalarAlgebra (R := D) m).toSMul
        let : IsScalarTower D K' M :=
          IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
        (Localization.awayMap
          ((algebraMap D (integralClosure D M)).comp
            ((algebraMap B D).comp (algebraMap R B)))
          (algebraMap A R f)).Etale →
        IsUnit (N : R) := by
  classical
  intro e N
  have he : ∀ k, 0 < e k :=
    heightTwoOtherBranchGaloisRamificationIndex_pos
      (K := K) (L := L) t hNC i
  have hN : 0 < N :=
    heightTwoSelectedBranchGaloisRamificationIndex_pos
      (K := K) (L := L) t hNC i
  rcases
      splitStrictNormalCrossings_heightTwo_galoisFullRootCover_fixedComponent_etale
        (K := K) (L := L) hNC i hi P hP htiP hCharZero hAwayBase with
    ⟨σ, hgeometryD, hlocal⟩
  refine ⟨σ, ?_⟩
  intro R n a B y F D
  refine ⟨hgeometryD.2.1, ?_⟩
  intro domainD K' algebraRK fractionRK algebraKK' m hm maximalM M
    algebraDM smulDM towerDK'M hAwayFull
  let hn : ∀ k, 0 < n k :=
    heightTwoConditionalOtherExponent_pos_of_pos t i r P e he σ
  let : FaithfulSMul K' M :=
    (faithfulSMul_iff_algebraMap_injective K' M).mpr
      (algebraMap K' M).injective
  let : FaithfulSMul D M := FaithfulSMul.trans D K' M
  have hEtale : Algebra.Etale D (integralClosure D M) :=
    hlocal m hm
  let boundary : Fin (d + 1) → R := fun j ↦
    if hj : j.1 < r then algebraMap A R (t j) else 1
  have hBoundaryPrimeOrUnit :
      ∀ j, Prime (boundary j) ∨ IsUnit (boundary j) := by
    intro j
    by_cases hj : j.1 < r
    · simpa [boundary, hj] using
        prime_or_isUnit_algebraMap_localizationAtPrime P
          (hNC.2.2.2.1 j hj)
    · right
      simp [boundary, hj]
  have hBoundaryCharZero :
      ∀ j, Prime (boundary j) →
        CharZero (R ⧸ Ideal.span {boundary j}) := by
    intro j hjPrime
    by_cases hj : j.1 < r
    · have htPrime : Prime (t j) := hNC.2.2.2.1 j hj
      have htP : t j ∈ P := by
        by_contra htNot
        apply hjPrime.not_isUnit
        have hunit : IsUnit (algebraMap A R (t j)) :=
          (IsLocalization.AtPrime.isUnit_to_map_iff R P (t j)).2 htNot
        simpa [boundary, hj] using hunit
      have hjBoundary : boundary j = algebraMap A R (t j) := by
        simp [boundary, hj]
      rw [hjBoundary]
      exact
        charZero_quotient_algebraMap_localizationAtPrime
          P htPrime htP (hCharZero j hj)
    · have hjOne : boundary j = 1 := by simp [boundary, hj]
      rw [hjOne] at hjPrime
      exact (not_prime_one hjPrime).elim
  have hBoundaryAssociated :
      Associated (algebraMap A R f) (∏ j, boundary j) := by
    have hmap := hNC.2.2.2.2.1.map (algebraMap A R)
    have hmap' : Associated (algebraMap A R f)
        (∏ j with j.1 < r, algebraMap A R (t j)) := by
      simpa [boundaryProduct, boundaryIndices] using hmap
    rw [Finset.prod_filter] at hmap'
    simpa [boundary] using hmap'
  exact
    lastExponent_isUnit_of_iteratedRadical_integralClosure_etale_boundaryAway_primeOrUnit_universe
      (A := R) n a hn N hN y boundary hBoundaryPrimeOrUnit
        hBoundaryCharZero (algebraMap A R f) hBoundaryAssociated
        (L := M) hEtale hAwayFull

end EtaleFundamentalGroups.Kummer

end
