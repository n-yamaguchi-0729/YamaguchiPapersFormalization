/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.IntegralClosure.IntegralBase.BoundaryAway
import EtaleFundamentalGroups.Normalization.Localization.BoundaryAway
import EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.FullRootCover.FixedComponentExponentUnit

/-!
# Selected exponent units from fixed-component field comparisons

If the canonical right map from the original extension field to every fixed
full-root tensor component is bijective, the original primitive boundary-away
map transports first to that field component and then through the finite full
root base.  This supplies the exact composite away map required by the
last-exponent obstruction.
-/

noncomputable section

open Polynomial
open scoped BigOperators TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uA uK uL

/-- A sourced equality of every fixed full-root component with the original
extension field supplies the primitive composite away map internally and
forces the selected exact exponent to be a unit. -/
theorem
    galoisFullRootCover_fixedComponent_exponent_isUnit_of_rightMap_bijective
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
        let : Algebra L M := genericTensorFieldComponentRightAlgebra m
        Function.Bijective (algebraMap L M) → IsUnit (N : R) := by
  classical
  intro e N
  have he : ∀ k, 0 < e k :=
    heightTwoOtherBranchGaloisRamificationIndex_pos
      (K := K) (L := L) t hNC i
  have hN : 0 < N :=
    heightTwoSelectedBranchGaloisRamificationIndex_pos
      (K := K) (L := L) t hNC i
  rcases
    splitStrictNormalCrossings_heightTwo_galoisFullRootCover_fixedComponent_selectedExponent_isUnit
        (K := K) (L := L) hNC i hi P hP htiP hCharZero hAwayBase with
    ⟨σ, hdomainD, hterminal⟩
  refine ⟨σ, ?_⟩
  intro R n a B y F D
  refine ⟨hdomainD, ?_⟩
  intro domainD K' algebraRK fractionRK algebraKK' m hm maximalM M algebraLM hbij
  let hn : ∀ k, 0 < n k :=
    heightTwoConditionalOtherExponent_pos_of_pos t i r P e he σ
  let : Module.Finite R B := finite_iteratedRadical n a hn
  let : Module.Finite B D :=
    (monic_X_pow_sub_C (algebraMap R B y) hN.ne').finite_adjoinRoot
  let : Module.Finite R D := Module.Finite.trans B D
  let : IsScalarTower R K K' :=
    galoisFullRootCoverFractionField_isScalarTower n a hn N hN y
  let : Algebra D M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := D) m
  let : SMul D M :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := D) m).toSMul
  let : IsScalarTower D K' M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower K L M :=
    genericTensorFieldComponent_right_isScalarTower m
  let : IsScalarTower K K' M :=
    genericTensorFieldComponent_isScalarTower m
  let : Algebra R L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A R L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let : IsScalarTower R K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  let : Algebra R M :=
    ((algebraMap L M).comp (algebraMap R L)).toAlgebra
  let : SMul R M :=
    (((algebraMap L M).comp (algebraMap R L)).toAlgebra).toSMul
  let : IsScalarTower R L M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R D M := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change algebraMap L M (algebraMap R L z) =
      algebraMap D M (algebraMap R D z)
    calc
      algebraMap L M (algebraMap R L z) =
          algebraMap L M (algebraMap K L (algebraMap R K z)) := by
        rw [IsScalarTower.algebraMap_apply R K L]
      _ = algebraMap K M (algebraMap R K z) :=
        (IsScalarTower.algebraMap_apply K L M (algebraMap R K z)).symm
      _ = algebraMap K' M (algebraMap K K' (algebraMap R K z)) :=
        IsScalarTower.algebraMap_apply K K' M (algebraMap R K z)
      _ = algebraMap K' M (algebraMap R K' z) := by
        rw [IsScalarTower.algebraMap_apply R K K']
      _ = algebraMap K' M (algebraMap D K' (algebraMap R D z)) := by
        rw [IsScalarTower.algebraMap_apply R D K']
      _ = algebraMap D M (algebraMap R D z) :=
        (IsScalarTower.algebraMap_apply D K' M (algebraMap R D z)).symm
  apply hterminal m hm
  have hAwayR :=
    normalizationLocalization_boundaryAway
      (K := K) (L := L) P f hAwayBase
  have hAwayFull :=
    integralClosure_integralBase_boundaryAway_comp_of_bijective_fieldTower_algebraMap
      (A := R) (B := D) (Omega := L) (P := M)
      hbij (algebraMap A R f) hAwayR
  exact hAwayFull

end EtaleFundamentalGroups.Kummer

end
