/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.OfFieldTower
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.FullRootCover.FixedComponent.FieldBijectiveExponentUnit

/-!
# The full-root exponent obstruction from an honest target-field action

An action of the full radical fraction field on the original target field
selects a canonical multiplication component of their tensor product.  The
right coordinate of that component is automatically an isomorphism: this is
a consequence of the action, not a component-comparison hypothesis.

This file packages that observation for the strict-normal-crossings
exponent obstruction.  It leaves exactly the construction of the honest
full-root action to the root producer; right-coordinate bijectivity,
component equality, degree equality, and local etaleness are all produced
internally.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uK uK' uL

/-- In the tensor component selected by an existing field-tower action, the
canonical right coordinate is bijective.

The inverse is the quotient equivalence induced by multiplication. -/
theorem fieldTowerTensorComponent_rightAlgebraMap_bijective
    {K : Type uK} {K' : Type uK'} {L : Type uL}
    [Field K] [Field K'] [Field L]
    [Algebra K K'] [Algebra K L]
    [Algebra K' L] [IsScalarTower K K' L] :
    let m := fieldTowerTensorComponentIdeal
      (K := K) (K' := K') (L := L)
    let : m.IsMaximal :=
      fieldTowerTensorComponentIdeal_isMaximal
        (K := K) (K' := K') (L := L)
    let M := GenericTensorFieldComponent m
    let : Algebra L M := genericTensorFieldComponentRightAlgebra m
    Function.Bijective (algebraMap L M) := by
  intro m maximalM M algebraLM
  let e : M ≃ₐ[K'] L :=
    fieldTowerTensorComponentAlgEquiv
      (K := K) (K' := K') (L := L)
  have he (z : L) : e (algebraMap L M z) = z := by
    change e (Ideal.Quotient.mk m ((1 : K') ⊗ₜ[K] z)) = z
    change fieldTowerTensorProductMap
      (K := K) (K' := K') (L := L) ((1 : K') ⊗ₜ[K] z) = z
    simp [fieldTowerTensorProductMap,
      Algebra.TensorProduct.productMap_apply_tmul]
  constructor
  · exact (algebraMap L M).injective
  · intro z
    refine ⟨e z, ?_⟩
    apply e.injective
    exact he (e z)

namespace Kummer

open Polynomial

universe uA

/-- Once the exact full-root fraction field acts on the original target
field, the selected branch exponent is a unit.

The multiplication kernel selects the fixed component internally and
`fieldTowerTensorComponent_rightAlgebraMap_bijective` discharges the old
right-coordinate callback.  Fixed-component purity and the primitive
normalization Away map remain source-produced by the imported obstruction
theorem. -/
theorem
    galoisFullRootCover_exponent_isUnit_of_targetFieldAction
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
      ∀ [Algebra K' L] [IsScalarTower K K' L], IsUnit (N : R) := by
  classical
  intro e N
  rcases
      galoisFullRootCover_fixedComponent_exponent_isUnit_of_rightMap_bijective
        (K := K) (L := L) hNC i hi P hP htiP hCharZero hAwayBase with
    ⟨σ, hdomainD, hterminal⟩
  refine ⟨σ, ?_⟩
  intro R n a B y F D
  refine ⟨hdomainD, ?_⟩
  intro domainD K' algebraRK fractionRK algebraKK' algebraK'L towerKK'L
  exact hterminal
    (fieldTowerTensorComponentIdeal (K := K) (K' := K') (L := L))
    (fieldTowerTensorComponentIdeal_isMaximal
      (K := K) (K' := K') (L := L))
    (fieldTowerTensorComponent_rightAlgebraMap_bijective
      (K := K) (K' := K') (L := L))

end Kummer

end EtaleFundamentalGroups

end
