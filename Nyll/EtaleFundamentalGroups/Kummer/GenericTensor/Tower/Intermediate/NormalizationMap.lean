/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.Tower
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product
import Nyll.SchemeTheory.Normalization.CompositumEmbedding

/-!
# The normalization map on an intermediate tensor component

A selected component of `F' \otimes[K] L` canonically contracts to a
component of `F \otimes[K] L`.  This file constructs the induced field map
over the smaller integral base and the resulting map between normalizations.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uA uB uK uF uF' uL

variable {A : Type uA} {B : Type uB}
variable {K : Type uK} {F : Type uF} {F' : Type uF'} {L : Type uL}
variable [CommRing A] [CommRing B]
variable [Field K] [Field F] [Field F'] [Field L]
variable [Algebra K F] [Algebra F F'] [Algebra K F']
variable [IsScalarTower K F F'] [Algebra K L]
variable [Algebra A F] [Algebra A F'] [IsScalarTower A F F']
variable [Algebra A B] [Algebra.IsIntegral A B]
variable [Algebra B F'] [IsScalarTower A B F']

/-- The canonical embedding from the intermediate component selected by
`m` into the final component, read over the smaller integral base `A`.

Both algebra structures are the literal left-factor structures. -/
noncomputable def
    genericTensorTowerIntermediateComponentAlgHomRestrictBase
    [FiniteDimensional F F']
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal] :
    let n := genericTensorTowerIntermediateIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    let M₀ := GenericTensorFieldComponent n
    let M := GenericTensorFieldComponent m
    letI : Algebra A M₀ :=
      genericTensorFieldComponentLeftScalarAlgebra (R := A) n
    letI : Algebra A M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := A) m
    M₀ →ₐ[A] M := by
  dsimp only
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  letI : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  let M₀ := GenericTensorFieldComponent n
  let M := GenericTensorFieldComponent m
  letI : Algebra A M₀ :=
    genericTensorFieldComponentLeftScalarAlgebra (R := A) n
  letI : Algebra A M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := A) m
  letI : Algebra F M :=
    genericTensorTowerFinalComponentAlgebra
      (K := K) (F := F) (F' := F') (L := L) m
  let f : M₀ →ₐ[F] M :=
    genericTensorTowerIntermediateComponentAlgHom
      (K := K) (F := F) (F' := F') (L := L) m
  exact
    { f.toRingHom with
      commutes' := by
        intro x
        change
          f (algebraMap F M₀ (algebraMap A F x)) =
            genericTensorFieldComponentLeft m (algebraMap A F' x)
        rw [f.commutes]
        change
          genericTensorFieldComponentLeft m
              (algebraMap F F' (algebraMap A F x)) =
            genericTensorFieldComponentLeft m (algebraMap A F' x)
        rw [IsScalarTower.algebraMap_apply A F F'] }

/-- The canonical normalization map attached to the same literal final
component `m` and its canonical intermediate contraction. -/
noncomputable def
    genericTensorTowerIntermediateNormalizationAlgHom
    [FiniteDimensional F F']
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal] :
    let n := genericTensorTowerIntermediateIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    let M₀ := GenericTensorFieldComponent n
    let M := GenericTensorFieldComponent m
    letI : Algebra A M₀ :=
      genericTensorFieldComponentLeftScalarAlgebra (R := A) n
    letI : Algebra A M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := A) m
    letI : SMul A M :=
      (genericTensorFieldComponentLeftScalarAlgebra (R := A) m).toSMul
    letI : Algebra B M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    letI : SMul B M :=
      (genericTensorFieldComponentLeftScalarAlgebra (R := B) m).toSMul
    letI : IsScalarTower A B M :=
      IsScalarTower.of_algebraMap_eq fun x ↦ by
        change
          genericTensorFieldComponentLeft m (algebraMap A F' x) =
            genericTensorFieldComponentLeft m
              (algebraMap B F' (algebraMap A B x))
        rw [IsScalarTower.algebraMap_apply A B F']
    integralClosure A M₀ →ₐ[A] integralClosure B M := by
  dsimp only
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  letI : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  let M₀ := GenericTensorFieldComponent n
  let M := GenericTensorFieldComponent m
  letI : Algebra A M₀ :=
    genericTensorFieldComponentLeftScalarAlgebra (R := A) n
  letI : Algebra A M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := A) m
  letI : SMul A M :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := A) m).toSMul
  letI : Algebra B M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := B) m
  letI : SMul B M :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := B) m).toSMul
  letI : IsScalarTower A B M :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change
        genericTensorFieldComponentLeft m (algebraMap A F' x) =
          genericTensorFieldComponentLeft m
            (algebraMap B F' (algebraMap A B x))
      rw [IsScalarTower.algebraMap_apply A B F']
  let f : M₀ →ₐ[A] M :=
    genericTensorTowerIntermediateComponentAlgHomRestrictBase
      (A := A) (K := K) (F := F) (F' := F') (L := L) m
  exact integralClosureToCompositumAlgHom f

end EtaleFundamentalGroups.Kummer

end
