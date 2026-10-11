/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.ActiveRoot.LocalizationEtale

/-!
# Compatibility of two chosen fraction-field actions

An injective map from a domain `D` into a field `L` extends canonically to a
chosen fraction field `K'` of `D`.  If `D` lies over another domain `R`, this
file records that the resulting `K'`-action is compatible with the already
chosen fraction field `K` of `R`.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe uR uD uK uK'

/-- Extending an injective `R`-algebra map `D → L` to a chosen fraction
field `K'` of `D` preserves the existing fraction-field tower `K → K'`.

The only map supplied as data is the integral root-ring map `ρ`; both its
faithful scalar action and the action of `K'` on `L` are constructed inside
the statement. -/
theorem
    chosenFractionFieldToFaithfulField_isScalarTower_of_fractionFieldTower
    {R : Type uR} {D L : Type uD} {K : Type uK} {K' : Type uK'}
    [CommRing R] [IsDomain R]
    [CommRing D] [IsDomain D] [Algebra R D]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra D K'] [IsFractionRing D K']
    [Algebra R K'] [IsScalarTower R D K']
    [Algebra K K'] [IsScalarTower R K K']
    [Field L] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L]
    (ρ : D →ₐ[R] L) (hρ : Function.Injective ρ) :
    let : Algebra D L := ρ.toRingHom.toAlgebra
    let : FaithfulSMul D L :=
      (faithfulSMul_iff_algebraMap_injective D L).mpr hρ
    let : Algebra K' L :=
      chosenFractionFieldToFaithfulFieldAlgebra
        (R := D) (K := K') (F := L)
    IsScalarTower K K' L := by
  intro algebraDL faithfulDL algebraK'L
  let : IsScalarTower R D L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (ρ.commutes x).symm
  let : IsScalarTower D K' L :=
    chosenFractionFieldToFaithfulField_isScalarTower
      (R := D) (K := K') (F := L)
  let : IsScalarTower R K' L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    calc
      algebraMap R L x = algebraMap D L (algebraMap R D x) :=
        IsScalarTower.algebraMap_apply R D L x
      _ = algebraMap K' L (algebraMap D K' (algebraMap R D x)) :=
        IsScalarTower.algebraMap_apply D K' L (algebraMap R D x)
      _ = algebraMap K' L (algebraMap R K' x) := by
        rw [IsScalarTower.algebraMap_apply R D K']
  apply IsScalarTower.of_algebraMap_eq
  intro x
  have hMaps : algebraMap K L =
      (algebraMap K' L).comp (algebraMap K K') := by
    apply IsFractionRing.ringHom_ext (A := R)
    intro y
    calc
      algebraMap K L (algebraMap R K y) = algebraMap R L y :=
        (IsScalarTower.algebraMap_apply R K L y).symm
      _ = algebraMap K' L (algebraMap R K' y) :=
        IsScalarTower.algebraMap_apply R K' L y
      _ = algebraMap K' L (algebraMap K K' (algebraMap R K y)) := by
        rw [← IsScalarTower.algebraMap_apply R K K']
  exact DFunLike.congr_fun hMaps x

end EtaleFundamentalGroups.Kummer
