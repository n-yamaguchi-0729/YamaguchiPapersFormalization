/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product

/-!
# The tensor component selected by an existing field-tower action

If `K'` already acts on `L` over `K`, multiplication gives a surjective map
`K' ⊗[K] L → L`.  Its kernel is therefore a maximal ideal, and the
corresponding generic tensor component is canonically `L` as a `K'`-algebra.

This is the component-selection producer used when a radical fraction field
has been embedded in the chosen normalization field.  The component and its
comparison equivalence are constructed from that action; neither is an
additional choice or an assumed comparison.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uB uK uK' uL

variable {K : Type uK} {K' : Type uK'} {L : Type uL}
variable [Field K] [Field K'] [Field L]
variable [Algebra K K'] [Algebra K L]
variable [Algebra K' L] [IsScalarTower K K' L]

/-- Multiplication after the given `K'`-action on `L`. -/
noncomputable def fieldTowerTensorProductMap :
    (K' ⊗[K] L) →ₐ[K'] L := by
  let g : (K' ⊗[K] L) →ₐ[K] L :=
    Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom K K' L)
      (AlgHom.id K L)
  exact
    { g.toRingHom with
      commutes' := by
        intro x
        simp [g, Algebra.TensorProduct.productMap_apply_tmul] }

/-- The tensor component cut out by the existing `K'`-action on `L`. -/
noncomputable def fieldTowerTensorComponentIdeal : Ideal (K' ⊗[K] L) :=
  RingHom.ker
    (fieldTowerTensorProductMap
      (K := K) (K' := K') (L := L)).toRingHom

/-- The multiplication map is onto, since every `l : L` is the image of
`1 ⊗ l`. -/
theorem fieldTowerTensorProductMap_surjective :
    Function.Surjective
      (fieldTowerTensorProductMap (K := K) (K' := K') (L := L)) := by
  intro l
  refine ⟨1 ⊗ₜ[K] l, ?_⟩
  simp [fieldTowerTensorProductMap,
    Algebra.TensorProduct.productMap_apply_tmul]

/-- The kernel of multiplication selects an actual field component. -/
theorem fieldTowerTensorComponentIdeal_isMaximal :
    (fieldTowerTensorComponentIdeal
      (K := K) (K' := K') (L := L)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective
    (fieldTowerTensorProductMap
      (K := K) (K' := K') (L := L)).toRingHom
    fieldTowerTensorProductMap_surjective

/-- The component selected by the tower action is the original ambient
field, compatibly with its `K'`-algebra structure. -/
noncomputable def fieldTowerTensorComponentAlgEquiv :
    let m := fieldTowerTensorComponentIdeal
      (K := K) (K' := K') (L := L)
    letI : m.IsMaximal :=
      fieldTowerTensorComponentIdeal_isMaximal
        (K := K) (K' := K') (L := L)
    GenericTensorFieldComponent m ≃ₐ[K'] L :=
  Ideal.quotientKerAlgEquivOfSurjective
    (f := fieldTowerTensorProductMap
      (K := K) (K' := K') (L := L))
    fieldTowerTensorProductMap_surjective

/-- Integral closures over any base acting through `K'` are identified on
the selected component and on the original ambient field.  The base action
on the component is the literal left-factor action. -/
noncomputable def fieldTowerTensorComponentIntegralClosureAlgEquiv
    {B : Type uB} [CommRing B]
    [Algebra B K'] [Algebra B L] [IsScalarTower B K' L] :
    let m := fieldTowerTensorComponentIdeal
      (K := K) (K' := K') (L := L)
    letI : m.IsMaximal :=
      fieldTowerTensorComponentIdeal_isMaximal
        (K := K) (K' := K') (L := L)
    let M := GenericTensorFieldComponent m
    letI : Algebra B M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    integralClosure B M ≃ₐ[B] integralClosure B L := by
  dsimp only
  let m := fieldTowerTensorComponentIdeal
    (K := K) (K' := K') (L := L)
  letI : m.IsMaximal :=
    fieldTowerTensorComponentIdeal_isMaximal
      (K := K) (K' := K') (L := L)
  let M := GenericTensorFieldComponent m
  letI : Algebra B M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := B) m
  let eK' : M ≃ₐ[K'] L :=
    fieldTowerTensorComponentAlgEquiv
      (K := K) (K' := K') (L := L)
  let eB : M ≃ₐ[B] L :=
    { toRingEquiv := eK'.toRingEquiv
      commutes' := by
        intro b
        change eK' (algebraMap K' M (algebraMap B K' b)) =
          algebraMap B L b
        rw [eK'.commutes]
        exact (IsScalarTower.algebraMap_apply B K' L b).symm }
  exact eB.mapIntegralClosure

/-- Pull a normalization prime on the ambient field back to the literal
tensor component selected by the field-tower action. -/
noncomputable def fieldTowerTensorComponentIntegralClosurePrime
    {B : Type uB} [CommRing B]
    [Algebra B K'] [Algebra B L] [IsScalarTower B K' L]
    (q : Ideal (integralClosure B L)) :
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
    (fieldTowerTensorComponentIntegralClosureAlgEquiv
      (B := B) (K := K) (K' := K') (L := L)).toRingHom

/-- Pullback along the produced normalization equivalence preserves
primality. -/
theorem fieldTowerTensorComponentIntegralClosurePrime_isPrime
    {B : Type uB} [CommRing B]
    [Algebra B K'] [Algebra B L] [IsScalarTower B K' L]
    (q : Ideal (integralClosure B L)) [q.IsPrime] :
    let m := fieldTowerTensorComponentIdeal
      (K := K) (K' := K') (L := L)
    letI : m.IsMaximal :=
      fieldTowerTensorComponentIdeal_isMaximal
        (K := K) (K' := K') (L := L)
    let M := GenericTensorFieldComponent m
    letI : Algebra B M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    (fieldTowerTensorComponentIntegralClosurePrime
      (B := B) (K := K) (K' := K') (L := L) q).IsPrime := by
  dsimp only
  exact Ideal.comap_isPrime
    (fieldTowerTensorComponentIntegralClosureAlgEquiv
      (B := B) (K := K) (K' := K') (L := L)).toRingHom q

/-- The chosen normalization localization on the produced tensor component
is the original chosen localization on the ambient field. -/
noncomputable def
    fieldTowerTensorComponentIntegralClosureLocalizationAlgEquiv
    {B : Type uB} [CommRing B]
    [Algebra B K'] [Algebra B L] [IsScalarTower B K' L]
    (q : Ideal (integralClosure B L)) [q.IsPrime] :
    let m := fieldTowerTensorComponentIdeal
      (K := K) (K' := K') (L := L)
    letI : m.IsMaximal :=
      fieldTowerTensorComponentIdeal_isMaximal
        (K := K) (K' := K') (L := L)
    let M := GenericTensorFieldComponent m
    letI : Algebra B M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    let p := fieldTowerTensorComponentIntegralClosurePrime
      (B := B) (K := K) (K' := K') (L := L) q
    letI : p.IsPrime :=
      fieldTowerTensorComponentIntegralClosurePrime_isPrime
        (B := B) (K := K) (K' := K') (L := L) q
    Localization.AtPrime p ≃ₐ[B] Localization.AtPrime q := by
  dsimp only
  let E := fieldTowerTensorComponentIntegralClosureAlgEquiv
    (B := B) (K := K) (K' := K') (L := L)
  let p := fieldTowerTensorComponentIntegralClosurePrime
    (B := B) (K := K) (K' := K') (L := L) q
  letI : p.IsPrime :=
    fieldTowerTensorComponentIntegralClosurePrime_isPrime
      (B := B) (K := K) (K' := K') (L := L) q
  exact Localization.localAlgEquiv p q E rfl

end EtaleFundamentalGroups

end
