/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.Tower.Intermediate.NormalizationMap

/-!
# Prime contraction on an intermediate tensor-component normalization

The normalization map selected by a literal final tensor component contracts
a specified final normalization prime.  Primality, maximality, and the exact
lies-over relation are derived from that same map.
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

/-- A ring map supplies the literal lies-over witness for contraction,
without asking typeclass search to reconstruct its induced algebra. -/
private theorem ringHomLiesOverComap
    {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (p : Ideal S) :
    letI : Algebra R S := g.toAlgebra
    p.LiesOver (p.comap g) :=
  by
    let : Algebra R S := g.toAlgebra
    exact ⟨rfl⟩

/-- The canonical normalization map with its scalar structure forgotten.
Keeping this projection as a source prevents downstream ideal operations
from reopening the quotient component's competing scalar-action instances. -/
@[reducible] noncomputable def
    genericTensorTowerIntermediateNormalizationRingHom
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
    letI : Algebra B M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    integralClosure A M₀ →+* integralClosure B M := by
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
  exact (genericTensorTowerIntermediateNormalizationAlgHom
    (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L) m).toRingHom

/-- Contract a specified normalization prime on the final component to the
normalization of the canonical intermediate component. -/
noncomputable def
    genericTensorTowerIntermediateNormalizationPrime
    [FiniteDimensional F F']
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal]
    (p :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M)) :
    let n := genericTensorTowerIntermediateIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    let M₀ := GenericTensorFieldComponent n
    letI : Algebra A M₀ :=
      genericTensorFieldComponentLeftScalarAlgebra (R := A) n
    Ideal (integralClosure A M₀) := by
  dsimp only at p ⊢
  exact p.comap
    (genericTensorTowerIntermediateNormalizationRingHom
      (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L) m)

omit [Algebra.IsIntegral A B] in
/-- Contracting along the public normalization algebra map gives the
canonical intermediate normalization prime.  This keeps downstream proofs
from unfolding the normalization map in a large instance context. -/
theorem genericTensorTowerIntermediateNormalizationAlgHom_comap_eq_prime
    [FiniteDimensional F F']
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal] :
    let M := GenericTensorFieldComponent m
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
    ∀ p : Ideal (integralClosure B M),
    p.comap
        (genericTensorTowerIntermediateNormalizationAlgHom
          (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L)
          m).toRingHom =
      genericTensorTowerIntermediateNormalizationPrime
        (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L)
        m p := by
  dsimp only
  intro p
  rfl

omit [Algebra.IsIntegral A B] in
/-- The exact contraction of a prime along the produced normalization map
is prime. -/
theorem genericTensorTowerIntermediateNormalizationPrime_isPrime
    [FiniteDimensional F F']
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal]
    (p :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M)) [p.IsPrime] :
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
      m p).IsPrime := by
  dsimp only at p ⊢
  exact Ideal.comap_isPrime
    (genericTensorTowerIntermediateNormalizationRingHom
      (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L) m) p

/-- A maximal final normalization prime contracts to a maximal prime on the
canonical intermediate normalization.  This uses integrality of `B / A`;
maximality is not a public comparison hypothesis. -/
theorem genericTensorTowerIntermediateNormalizationPrime_isMaximal
    [FiniteDimensional F F']
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
      m p).IsMaximal := by
  dsimp only at p ⊢
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  let : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  let M₀ := GenericTensorFieldComponent n
  let M := GenericTensorFieldComponent m
  let : Algebra A M₀ :=
    genericTensorFieldComponentLeftScalarAlgebra (R := A) n
  let : Algebra A M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := A) m
  let : SMul A M :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := A) m).toSMul
  let : Algebra B M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := B) m
  let : SMul B M :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := B) m).toSMul
  let : IsScalarTower A B M :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change
        genericTensorFieldComponentLeft m (algebraMap A F' x) =
          genericTensorFieldComponentLeft m
            (algebraMap B F' (algebraMap A B x))
      rw [IsScalarTower.algebraMap_apply A B F']
  let f : M₀ →ₐ[A] M :=
    genericTensorTowerIntermediateComponentAlgHomRestrictBase
      (A := A) (K := K) (F := F) (F' := F') (L := L) m
  let g : integralClosure A M₀ →ₐ[A] integralClosure B M :=
    integralClosureToCompositumAlgHom f
  let : Algebra (integralClosure A M₀) (integralClosure B M) :=
    g.toAlgebra
  let : Algebra.IsIntegral (integralClosure A M₀)
      (integralClosure B M) :=
    integralClosureToCompositum_isIntegral f
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (algebraMap (integralClosure A M₀) (integralClosure B M))
    (fun x ↦ Algebra.IsIntegral.isIntegral x) p

omit [Algebra.IsIntegral A B] in
/-- With the produced normalization-map algebra structure, the specified
final prime lies over its literal contraction. -/
theorem genericTensorTowerIntermediateNormalizationPrime_liesOver
    [FiniteDimensional F F']
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal]
    (p :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M)) :
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
    p.LiesOver
      (genericTensorTowerIntermediateNormalizationPrime
      (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L)
      m p) := by
  dsimp only at p ⊢
  let g := genericTensorTowerIntermediateNormalizationRingHom
    (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L) m
  exact ringHomLiesOverComap g p

end EtaleFundamentalGroups.Kummer

end
