/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GenericTensor.FieldComponent.OfFieldTower
import SchemeTheory.Normalization.IntegralClosure.IntegralBase.Equiv

/-!
# A field-tower component over an integral root base

Suppose an integral enlargement `A → B` acts on the same field `L`, and the
fraction field used on the left of a generic tensor product already acts on
`L`.  The multiplication component is then literally `L`.  Combining that
produced component equivalence with invariance of integral closure under the
integral base enlargement identifies its `B`-normalization with the original
`A`-normalization.

The final localization comparison transports a specified prime through this
canonical composite.  This is the comparison plumbing needed after an exact
full-root action has been source-produced.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uA uB uK uK' uL

variable {A : Type uA} {B : Type uB}
variable {K : Type uK} {K' : Type uK'} {L : Type uL}
variable [CommRing A] [CommRing B]
variable [Field K] [Field K'] [Field L]
variable [Algebra K K'] [Algebra K L]
variable [Algebra K' L] [IsScalarTower K K' L]
variable [Algebra A B] [Algebra A L] [Algebra B L]
variable [IsScalarTower A B L] [Algebra.IsIntegral A B]
variable [Algebra B K'] [IsScalarTower B K' L]

/-- The normalization of the produced multiplication component over the
integral root base is the original normalization over the smaller base. -/
noncomputable def fieldTowerTensorComponentIntegralBaseAlgEquiv :
    let m := fieldTowerTensorComponentIdeal
      (K := K) (K' := K') (L := L)
    letI : m.IsMaximal :=
      fieldTowerTensorComponentIdeal_isMaximal
        (K := K) (K' := K') (L := L)
    let M := GenericTensorFieldComponent m
    letI : Algebra B M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    letI : Algebra B (integralClosure A L) :=
      integralClosureIntegralBaseAlgebra
    integralClosure B M ≃ₐ[B] integralClosure A L := by
  dsimp only
  let m := fieldTowerTensorComponentIdeal
    (K := K) (K' := K') (L := L)
  letI : m.IsMaximal :=
    fieldTowerTensorComponentIdeal_isMaximal
      (K := K) (K' := K') (L := L)
  let M := GenericTensorFieldComponent m
  letI : Algebra B M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := B) m
  letI : Algebra B (integralClosure A L) :=
    integralClosureIntegralBaseAlgebra
  exact
    (fieldTowerTensorComponentIntegralClosureAlgEquiv
      (B := B) (K := K) (K' := K') (L := L)).trans
        (integralClosureIntegralBaseAlgEquiv
          (A := A) (B := B) (L := L))

/-- Pull an original normalization prime back to the normalization of the
literal multiplication component over the integral root base. -/
noncomputable def fieldTowerTensorComponentIntegralBasePrime
    (q : Ideal (integralClosure A L)) :
    let m := fieldTowerTensorComponentIdeal
      (K := K) (K' := K') (L := L)
    letI : m.IsMaximal :=
      fieldTowerTensorComponentIdeal_isMaximal
        (K := K) (K' := K') (L := L)
    let M := GenericTensorFieldComponent m
    letI : Algebra B M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    Ideal (integralClosure B M) := by
  dsimp only
  exact q.comap
    (fieldTowerTensorComponentIntegralBaseAlgEquiv
      (A := A) (B := B) (K := K) (K' := K') (L := L)).toRingHom

/-- The pulled-back prime is prime. -/
theorem fieldTowerTensorComponentIntegralBasePrime_isPrime
    (q : Ideal (integralClosure A L)) [q.IsPrime] :
    let m := fieldTowerTensorComponentIdeal
      (K := K) (K' := K') (L := L)
    letI : m.IsMaximal :=
      fieldTowerTensorComponentIdeal_isMaximal
        (K := K) (K' := K') (L := L)
    let M := GenericTensorFieldComponent m
    letI : Algebra B M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    (fieldTowerTensorComponentIntegralBasePrime
      (A := A) (B := B) (K := K) (K' := K') (L := L) q).IsPrime := by
  dsimp only
  exact Ideal.comap_isPrime
    (fieldTowerTensorComponentIntegralBaseAlgEquiv
      (A := A) (B := B) (K := K) (K' := K') (L := L)).toRingHom q

/-- Localization at the pulled-back full-component prime is canonically the
original chosen normalization localization. -/
noncomputable def
    fieldTowerTensorComponentIntegralBaseLocalizationAlgEquiv
    (q : Ideal (integralClosure A L)) [q.IsPrime] :
    let m := fieldTowerTensorComponentIdeal
      (K := K) (K' := K') (L := L)
    letI : m.IsMaximal :=
      fieldTowerTensorComponentIdeal_isMaximal
        (K := K) (K' := K') (L := L)
    let M := GenericTensorFieldComponent m
    letI : Algebra B M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    letI : Algebra B (integralClosure A L) :=
      integralClosureIntegralBaseAlgebra
    let p := fieldTowerTensorComponentIntegralBasePrime
      (A := A) (B := B) (K := K) (K' := K') (L := L) q
    letI : p.IsPrime :=
      fieldTowerTensorComponentIntegralBasePrime_isPrime
        (A := A) (B := B) (K := K) (K' := K') (L := L) q
    Localization.AtPrime p ≃ₐ[B] Localization.AtPrime q := by
  dsimp only
  let E := fieldTowerTensorComponentIntegralBaseAlgEquiv
    (A := A) (B := B) (K := K) (K' := K') (L := L)
  let p := fieldTowerTensorComponentIntegralBasePrime
    (A := A) (B := B) (K := K) (K' := K') (L := L) q
  letI : p.IsPrime :=
    fieldTowerTensorComponentIntegralBasePrime_isPrime
      (A := A) (B := B) (K := K) (K' := K') (L := L) q
  letI : Algebra B (integralClosure A L) :=
    integralClosureIntegralBaseAlgebra
  exact Localization.localAlgEquiv p q E rfl

end EtaleFundamentalGroups

end
