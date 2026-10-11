/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.BaseChange.GenericFiber
import SchemeTheory.RingTheory.GenericFiber.Finite
import EtaleFundamentalGroups.GenericTensor.FieldComponent.Basic

/-!
# Fixed tensor components after finite-etale base change

Let `T / A` be finite etale and let `E / F` be its generic fibre, where
`F` and `E` are fraction fields of `A` and `T`.  After replacing `A` by a
normal domain `B` with fraction field `K`, a specified maximal ideal of
`K tensor[F] E` selects an actual field component.  The normalization of
`B` in that same component is finite etale.

This is the component-preserving form used on the complement of the boundary:
the maximal ideal is data produced by the global chosen component, rather
than an abstract field or a postulated comparison isomorphism.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uA uB uT uF uE uK uR uC

/-- A specified generic tensor component of a finite-etale algebra remains
finite etale after normalization over a normal base change.

The generic-fibre equivalence, the iterated base-change equivalence, and the
surjection to the selected quotient component are all constructed in the
proof. -/
theorem integralClosure_genericTensorFieldComponent_etale_of_finiteEtale_baseChange
    {A : Type uA} {B : Type uB} {T : Type uT}
    {F : Type uF} {E : Type uE} {K : Type uK}
    [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B]
    [CommRing T] [IsDomain T] [Algebra A T]
    [Module.Finite A T] [Algebra.Etale A T]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field E] [Algebra T E] [IsFractionRing T E]
    [Algebra A E] [IsScalarTower A T E]
    [Algebra F E] [IsScalarTower A F E]
    [Field K] [Algebra B K] [IsFractionRing B K]
    [Algebra A K] [Algebra F K]
    [IsScalarTower A B K] [IsScalarTower A F K]
    (m : Ideal (K ⊗[F] E)) [m.IsMaximal] :
    let M := GenericTensorFieldComponent m
    Algebra.Etale B (integralClosure B M) := by
  let M := GenericTensorFieldComponent m
  let : IsScalarTower B K M := inferInstance
  let eGeneric : (F ⊗[A] T) ≃ₐ[F] E :=
    finiteGenericFiberAlgEquiv (R := A) (C := T) (K := F) (E := E)
  let eFactor : (K ⊗[A] T) ≃ₐ[K] (K ⊗[F] E) :=
    iteratedGenericFiberEquiv A F K T E eGeneric
  let quotient : (K ⊗[F] E) →ₐ[K] M :=
    Ideal.Quotient.mkₐ K m
  let componentMap : (K ⊗[A] T) →ₐ[K] M :=
    quotient.comp eFactor.toAlgHom
  apply integralClosure_etale_of_surjective_reassociatedGenericFiber
    (A := A) (B := B) (T := T) (K := K) componentMap
  exact Ideal.Quotient.mk_surjective.comp eFactor.surjective

/-- Away-branch form of
`integralClosure_genericTensorFieldComponent_etale_of_finiteEtale_baseChange`.

If `f` is a unit on the new normal base `B`, the map from `R` to `B`
extends canonically across `R[1/f]`.  The induced embedding of its fraction
field into `Frac(B)` and all scalar towers are constructed in the proof.  A
specified maximal ideal of the resulting generic tensor product therefore
gives an etale normalization over `B` without postulating a field-component
comparison. -/
theorem integralClosure_genericTensorFieldComponent_etale_of_away_isUnit
    {R : Type uR} {C : Type uC} {B : Type uB}
    {F : Type uF} {E : Type uE} {K : Type uK}
    [CommRing R] [IsDomain R]
    [CommRing C] [IsDomain C] [Algebra R C] [FaithfulSMul R C]
    (f : R)
    [Algebra (Localization.Away f)
      (Localization.Away (algebraMap R C f))]
    [Module.Finite (Localization.Away f)
      (Localization.Away (algebraMap R C f))]
    [Algebra.Etale (Localization.Away f)
      (Localization.Away (algebraMap R C f))]
    [Field F] [Algebra (Localization.Away f) F]
    [IsFractionRing (Localization.Away f) F]
    [Algebra R F] [IsScalarTower R (Localization.Away f) F]
    [Field E] [Algebra (Localization.Away (algebraMap R C f)) E]
    [IsFractionRing (Localization.Away (algebraMap R C f)) E]
    [Algebra (Localization.Away f) E]
    [IsScalarTower (Localization.Away f)
      (Localization.Away (algebraMap R C f)) E]
    [Algebra F E] [IsScalarTower (Localization.Away f) F E]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra R B]
    (hf : IsUnit (algebraMap R B f))
    [Field K] [Algebra B K] [IsFractionRing B K]
    [Algebra R K] [IsScalarTower R B K]
    [Algebra F K] [IsScalarTower R F K]
    (m : Ideal (K ⊗[F] E)) [m.IsMaximal] :
    Algebra.Etale B
      (integralClosure B (GenericTensorFieldComponent m)) := by
  let S := Localization.Away f
  let T := Localization.Away (algebraMap R C f)
  have hf0 : f ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hf
    exact not_isUnit_zero hf
  have hfC0 : algebraMap R C f ≠ 0 :=
    by simpa using (FaithfulSMul.algebraMap_injective R C).ne hf0
  let : IsDomain S := IsLocalization.Away.isDomain (S := S) hf0
  let : IsDomain T := IsLocalization.Away.isDomain (S := T) hfC0
  let mapSB : S →+* B := IsLocalization.Away.lift f hf
  let : Algebra S B := mapSB.toAlgebra
  let mapSK : S →+* K :=
    (algebraMap F K).comp (algebraMap S F)
  let : Algebra S K := mapSK.toAlgebra
  let : IsScalarTower S F K :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hmaps :
      (algebraMap B K).comp mapSB = mapSK := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext x
    simp only [RingHom.comp_apply]
    rw [show mapSB (algebraMap R S x) = algebraMap R B x by
      exact IsLocalization.Away.lift_eq f hf x]
    change algebraMap B K (algebraMap R B x) =
      algebraMap F K (algebraMap S F (algebraMap R S x))
    calc
      algebraMap B K (algebraMap R B x) = algebraMap R K x :=
        (IsScalarTower.algebraMap_apply R B K x).symm
      _ = algebraMap F K (algebraMap R F x) :=
        IsScalarTower.algebraMap_apply R F K x
      _ = algebraMap F K (algebraMap S F (algebraMap R S x)) :=
        congrArg (algebraMap F K)
          (IsScalarTower.algebraMap_apply R S F x)
  let : IsScalarTower S B K :=
    IsScalarTower.of_algebraMap_eq' hmaps.symm
  exact
    integralClosure_genericTensorFieldComponent_etale_of_finiteEtale_baseChange
      (A := S) (B := B) (T := T) (F := F) (E := E) (K := K) m

end EtaleFundamentalGroups

end
