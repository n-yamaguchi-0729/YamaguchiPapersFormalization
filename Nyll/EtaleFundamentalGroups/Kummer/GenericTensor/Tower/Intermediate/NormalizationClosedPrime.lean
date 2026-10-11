/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.Tower.Intermediate.NormalizationPrime

/-!
# The closed prime on an intermediate tensor-component normalization

A maximal prime on the final normalization contracts to the closed point of
the canonical intermediate normalization.  The same literal final component,
normalization map, and prime are retained throughout.
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

/-- If the smaller base is local, a maximal final normalization prime
contracts to the closed point of the canonical intermediate normalization.

The closed-prime assertion is produced from the two integral extensions; no
prime equality is supplied by the caller. -/
theorem
    genericTensorTowerIntermediateNormalizationPrime_liesOver_maximalIdeal
    [IsLocalRing A] [FiniteDimensional F F']
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal]
    (p :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M)) [p.IsMaximal] :
    let n := genericTensorTowerIntermediateIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    let M₀ := GenericTensorFieldComponent n
    letI : Algebra A M₀ :=
      genericTensorFieldComponentLeftScalarAlgebra (R := A) n
    (genericTensorTowerIntermediateNormalizationPrime
      (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L)
      m p).LiesOver (IsLocalRing.maximalIdeal A) := by
  dsimp only at p ⊢
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  let : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  let M₀ := GenericTensorFieldComponent n
  let : Algebra A M₀ :=
    genericTensorFieldComponentLeftScalarAlgebra (R := A) n
  let q := genericTensorTowerIntermediateNormalizationPrime
    (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L)
    m p
  let : q.IsMaximal :=
    genericTensorTowerIntermediateNormalizationPrime_isMaximal
      (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L)
      m p
  let : Algebra.IsIntegral A (integralClosure A M₀) :=
    IsIntegralClosure.isIntegral_algebra A M₀
  have hUnder : (q.under A).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (algebraMap A (integralClosure A M₀)) (fun x ↦ Algebra.IsIntegral.isIntegral x) q
  exact ⟨(IsLocalRing.eq_maximalIdeal hUnder).symm⟩

/-- The reusable same-`m`/same-`p` package: the canonical intermediate
ideal, the induced normalization map, and the exact contraction of the
specified final prime are returned together with all closed-prime geometry.

This is the input shape needed when a completed chosen factor is first
identified at the final component and then contracted to the prefix
component. -/
theorem genericTensorTowerIntermediateNormalizationClosedPrime_geometry
    [IsLocalRing A] [FiniteDimensional F F']
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal]
    (p :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M)) [p.IsMaximal] :
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
    let g := genericTensorTowerIntermediateNormalizationAlgHom
      (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L) m
    letI : Algebra (integralClosure A M₀) (integralClosure B M) :=
      g.toAlgebra
    let q := genericTensorTowerIntermediateNormalizationPrime
      (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L)
      m p
    q.IsMaximal ∧ q.LiesOver (IsLocalRing.maximalIdeal A) ∧
      p.LiesOver q := by
  dsimp only
  exact ⟨
    genericTensorTowerIntermediateNormalizationPrime_isMaximal
      (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L)
      m p,
    genericTensorTowerIntermediateNormalizationPrime_liesOver_maximalIdeal
      (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L)
      m p,
    genericTensorTowerIntermediateNormalizationPrime_liesOver
      (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L)
      m p⟩

end EtaleFundamentalGroups.Kummer

end
