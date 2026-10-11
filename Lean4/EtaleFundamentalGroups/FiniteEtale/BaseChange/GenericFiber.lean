/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ValuedFieldTheory.Valuation.DiscreteValuationField.Compositum
import Mathlib.RingTheory.TensorProduct.Finite
import EtaleFundamentalGroups.FiniteEtale.GenericFiber.Component

/-!
# Selected generic components after finite-etale base change

This file packages the generic-fibre bookkeeping needed after a finite-etale
base change.  The generic fibre of `B ⊗[A] T` over a fraction field `K` of
`B` is canonically `K ⊗[A] T`.  A surjective map from that tensor product to
a field selects a maximal component by its kernel.  The normalization of the
selected field is finite etale over `B`.

The final theorem specializes the target field to an actual compositum in a
fixed ambient field, using the product-map API from ClassFieldTheory.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe uA uB uT uK uF uE uΩ

/-- Reassociate the generic fibre of a base-changed algebra:
`(B ⊗[A] T) ⊗[B] K ≃ K ⊗[A] T`.

The source uses the right `K`-algebra structure. -/
def baseChangeGenericFiberEquiv
    (A : Type uA) (B : Type uB) (T : Type uT) (K : Type uK)
    [CommRing A] [CommRing B] [CommRing T] [CommRing K]
    [Algebra A B] [Algebra A T] [Algebra B K]
    [Algebra A K] [IsScalarTower A B K] :
    letI : Algebra K ((B ⊗[A] T) ⊗[B] K) :=
      Algebra.TensorProduct.rightAlgebra
    ((B ⊗[A] T) ⊗[B] K) ≃ₐ[K] (K ⊗[A] T) := by
  letI : Algebra K ((B ⊗[A] T) ⊗[B] K) :=
    Algebra.TensorProduct.rightAlgebra
  exact
    (Algebra.TensorProduct.commRight B K (B ⊗[A] T)).symm.trans
      (Algebra.TensorProduct.cancelBaseChange A B K K T)

/-- If the generic fibre of `T / A` is identified with `E / F`, extending
the fraction field from `F` to `K` identifies `K ⊗[A] T` with
`K ⊗[F] E`. -/
def iteratedGenericFiberEquiv
    (A : Type uA) (F : Type uF) (K : Type uK)
    (T : Type uT) (E : Type uE)
    [CommRing A] [CommRing F] [CommRing K] [CommRing T] [CommRing E]
    [Algebra A F] [Algebra A K] [Algebra F K] [IsScalarTower A F K]
    [Algebra A T] [Algebra F E]
    (e : (F ⊗[A] T) ≃ₐ[F] E) :
    (K ⊗[A] T) ≃ₐ[K] (K ⊗[F] E) :=
  (Algebra.TensorProduct.cancelBaseChange A F K K T).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e)

/-- The kernel of a map from a generic fibre to a specified field. -/
abbrev selectedGenericFiberIdeal
    {R : Type uA} {T : Type uT} {K : Type uK} {Ω : Type uΩ}
    [CommRing R] [CommRing T] [Algebra R T]
    [CommRing K] [Algebra R K]
    [CommRing Ω] [Algebra R Ω]
    (f : (T ⊗[R] K) →ₐ[R] Ω) : Ideal (T ⊗[R] K) :=
  RingHom.ker f

/-- A surjective generic-fibre map to a field selects a maximal ideal. -/
theorem selectedGenericFiberIdeal_isMaximal
    {R : Type uA} {T : Type uT} {K : Type uK} {Ω : Type uΩ}
    [CommRing R] [CommRing T] [Algebra R T]
    [CommRing K] [Algebra R K]
    [Field Ω] [Algebra R Ω]
    (f : (T ⊗[R] K) →ₐ[R] Ω) (hf : Function.Surjective f) :
    (selectedGenericFiberIdeal f).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective f hf

/-- The component selected by a surjective generic-fibre map is the target
field itself. -/
def selectedGenericFiberComponentEquiv
    {R : Type uA} {T : Type uT} {K : Type uK} {Ω : Type uΩ}
    [CommRing R] [CommRing T] [Algebra R T]
    [CommRing K] [Algebra R K]
    [Field Ω] [Algebra R Ω]
    (f : (T ⊗[R] K) →ₐ[R] Ω) (hf : Function.Surjective f) :
    ((T ⊗[R] K) ⧸ selectedGenericFiberIdeal f) ≃ₐ[R] Ω := by
  simpa only [selectedGenericFiberIdeal] using
    (Ideal.quotientKerAlgEquivOfSurjective (f := f) hf)

/-- A specified field quotient of the generic fibre of a finite-etale
algebra has finite-etale normalization over a normal base. -/
theorem integralClosure_etale_of_surjective_genericFiber
    {R : Type uA} {T : Type uT} {K : Type uK} {Ω : Type uΩ}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra R Ω]
    (f : (T ⊗[R] K) →ₐ[R] Ω) (hf : Function.Surjective f) :
    Algebra.Etale R (integralClosure R Ω) := by
  let m := selectedGenericFiberIdeal f
  let : m.IsMaximal := selectedGenericFiberIdeal_isMaximal f hf
  have hComponent : Algebra.Etale R
      (integralClosure R (FiniteEtaleGenericFiberComponent m)) :=
    integralClosure_etale_genericFiberComponent m
  let e : FiniteEtaleGenericFiberComponent m ≃ₐ[R] Ω :=
    selectedGenericFiberComponentEquiv f hf
  exact Algebra.Etale.of_equiv e.mapIntegralClosure

/-- Reassociated form of
`integralClosure_etale_of_surjective_genericFiber`.

It is enough to give a surjective `K`-algebra map `K ⊗[A] T → Ω`; the
finite-etale algebra over `B` and its generic component are constructed in
the proof. -/
theorem integralClosure_etale_of_surjective_reassociatedGenericFiber
    {A : Type uA} {B : Type uB} {T : Type uT}
    {K : Type uK} {Ω : Type uΩ}
    [CommRing A] [CommRing B] [Algebra A B]
    [CommRing T] [Algebra A T] [Module.Finite A T] [Algebra.Etale A T]
    [IsDomain B] [IsIntegrallyClosed B]
    [Field K] [Algebra B K] [IsFractionRing B K]
    [Algebra A K] [IsScalarTower A B K]
    [Field Ω] [Algebra K Ω] [Algebra B Ω] [IsScalarTower B K Ω]
    (f : (K ⊗[A] T) →ₐ[K] Ω) (hf : Function.Surjective f) :
    Algebra.Etale B (integralClosure B Ω) := by
  let S := B ⊗[A] T
  let : Module.Finite B S := Module.Finite.base_change A B T
  let : Algebra.Etale B S := Algebra.Etale.baseChange A T B
  let : Algebra K (S ⊗[B] K) := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower B K (S ⊗[B] K) :=
    Algebra.TensorProduct.right_isScalarTower
  let e : (S ⊗[B] K) ≃ₐ[K] (K ⊗[A] T) :=
    baseChangeGenericFiberEquiv A B T K
  let gK : (S ⊗[B] K) →ₐ[K] Ω := f.comp e.toAlgHom
  let gB : (S ⊗[B] K) →ₐ[B] Ω := gK.restrictScalars B
  apply integralClosure_etale_of_surjective_genericFiber
    (R := B) (T := S) (K := K) gB
  exact hf.comp e.surjective

open DiscreteValuationField.FieldCompositum

/-- Actual-compositum endpoint.

Assume the generic fibre `F ⊗[A] T` is a field `E` inside a common ambient
field and that `K'` is the fraction field of the new normal base `B`.  Then
the integral closure of `B` in the actual compositum `E ⊔ K'` is finite
etale over `B`.
-/
theorem integralClosure_compositum_etale_of_finiteEtale_baseChange
    {A : Type uA} {B : Type uB} {T : Type uT}
    {F : Type uF} {Ω : Type uΩ}
    [CommRing A] [CommRing B] [Algebra A B]
    [CommRing T] [Algebra A T] [Module.Finite A T] [Algebra.Etale A T]
    [IsDomain B] [IsIntegrallyClosed B]
    [Field F] [Algebra A F]
    [Field Ω] [Algebra F Ω]
    (E K' : IntermediateField F Ω)
    [Algebra B K'] [IsFractionRing B K']
    [Algebra A K'] [IsScalarTower A B K'] [IsScalarTower A F K']
    [FiniteDimensional F E]
    (eGeneric : (F ⊗[A] T) ≃ₐ[F] E) :
    let M := E ⊔ K'
    letI : Algebra B M :=
      ((algebraMap K' M).comp (algebraMap B K')).toAlgebra
    Algebra.Etale B (integralClosure B M) := by
  let M := E ⊔ K'
  let : Algebra B M :=
    ((algebraMap K' M).comp (algebraMap B K')).toAlgebra
  let : IsScalarTower B K' M := IsScalarTower.of_algebraMap_eq' rfl
  let eFactor : (K' ⊗[A] T) ≃ₐ[K'] (K' ⊗[F] E) :=
    iteratedGenericFiberEquiv A F K' T E eGeneric
  let product : (K' ⊗[F] E) →ₐ[K'] M :=
    supFlipProductMapRightAlgHom E K'
  let f : (K' ⊗[A] T) →ₐ[K'] M := product.comp eFactor.toAlgHom
  apply integralClosure_etale_of_surjective_reassociatedGenericFiber
    (A := A) (B := B) (T := T) (K := K') f
  exact (supFlipProductMapRightAlgHom_surjective E K').comp
    eFactor.surjective

end EtaleFundamentalGroups

end
