/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.FullRootCover.FixedComponentEtale
import EtaleFundamentalGroups.Purity.SpecialLocal.DimensionTwo.IntegralClosure.Local

/-!
# Purity for a fixed component of the exact Galois full root cover

The exact full root cover is a two-dimensional regular local domain.  The
height-one analysis for a fixed generic tensor component therefore feeds
directly into local purity, giving etaleness of the whole normalization over
the cover.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe uA uK uL

/-- For every fixed generic tensor component of the exact Galois full root
cover, the normalization is etale over the full cover.  Regularity of the
cover and etaleness at all height-one localizations are produced internally
from the split strict-normal-crossings data. -/
theorem
    splitStrictNormalCrossings_heightTwo_galoisFullRootCover_fixedComponent_etale
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
    (hAway : (Localization.awayMap
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
      ∃ hgeometryD : IsRegularLocalRing D ∧ IsDomain D ∧
          ringKrullDim D = ((2 : ℕ∞) : WithBot ℕ∞),
        let : IsRegularLocalRing D := hgeometryD.1
        let : IsDomain D := hgeometryD.2.1
        let : IsIntegrallyClosed D :=
          SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
            hgeometryD.2.2
        let : Algebra R K :=
          localizationAtPrimeToFractionFieldAlgebra (K := K) P
        let : IsFractionRing R K :=
          localizationAtPrimeToFractionField_isFractionRing (K := K) P
        let K' := FractionRing D
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
          Algebra.Etale D (integralClosure D M) := by
  classical
  intro e N
  rcases
      splitStrictNormalCrossings_heightTwo_galoisFullRootCover_fixedComponent_heightOne_etale
        (K := K) (L := L) hNC i hi P hP htiP hCharZero hAway with
    ⟨σ, hgeometryD, hlocal⟩
  refine ⟨σ, ?_⟩
  intro R n a B y F D
  refine ⟨hgeometryD, ?_⟩
  intro regularD domainD closedD algebraRK fractionRK K' algebraKK' m hm
    maximalM M algebraDM smulDM towerDK'M
  apply
    SpecialLocalPurity.integralClosure_etale_of_isRegularLocalRing_dimension_two
      (A := D) (K := K') (L := M) hgeometryD.2.2
  intro q hqPrime hqHeight
  exact hlocal m hm q hqHeight

end EtaleFundamentalGroups.Kummer

end
