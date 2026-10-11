/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Completions.Chosen.GenericComponent
import SchemeTheory.Normalization.CompositumEmbedding

/-!
# A normalization prime selected by the completed generic component

Starting from the closed prime `Q`, the preceding completed-component
construction fixes a maximal ideal `m` of `K' ⊗[K] L`.  This file maps the
finite completed model `R' ⊗[R] C` into the field component selected by `m`,
then restricts the codomain to the integral closure of `R'` in that field.

The kernel is exactly the generic prime already selected below the completed
closed prime.  Consequently the integral map to the normalization admits a
maximal ideal above that same closed prime.  Thus neither the field component
nor the normalization prime is replaced by an unrelated branch.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uR' uC uK uL uK'

variable {R : Type uR} {R' : Type uR'} {C : Type uC}
variable [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [CommRing R'] [IsDomain R'] [IsLocalRing R'] [Algebra R R']
variable [IsLocalHom (algebraMap R R')] [Module.FaithfullyFlat R R']
variable [CommRing C] [IsDomain C] [Algebra R C] [Module.Finite R C]
variable [FaithfulSMul R C]

variable {K' : Type uK'} [Field K'] [Algebra R' K']
variable [IsFractionRing R' K']
variable {K : Type uK} {L : Type uL}
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra C L] [IsFractionRing C L]
variable [Algebra R L] [IsScalarTower R C L]
variable [Algebra K L] [IsScalarTower R K L]
variable [Algebra R K'] [IsScalarTower R R' K']
variable [Algebra K K'] [IsScalarTower R K K']

/-- The map from the finite completed model to a specified generic tensor
component.  Later it is applied to the component fixed by `Q`. -/
noncomputable def completedChosenComponentAlgHom
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] :
    completedFiniteBaseChange (R := R) (R' := R') (C := C) →ₐ[R']
      GenericTensorFieldComponent m :=
  ((Ideal.Quotient.mkₐ K' m).restrictScalars R').comp
    ((AlgHom.restrictScalars R'
      (completedGenericFiberEquiv
        (R := R) (R' := R') (C := C) (K := K) (L := L)
        (K' := K')).toAlgHom).comp
      (Algebra.TensorProduct.includeRight :
        completedFiniteBaseChange (R := R) (R' := R') (C := C) →ₐ[R']
          completedFiniteBaseChangeGenericFiber
            (R := R) (R' := R') (C := C) (K' := K')))

/-- Restrict the component map to the integral closure of `R'` in the
selected component.  Finiteness of the completed finite model supplies
integrality of every image. -/
noncomputable def completedChosenNormalizationAlgHom
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] :
    completedFiniteBaseChange (R := R) (R' := R') (C := C) →ₐ[R']
      integralClosure R' (GenericTensorFieldComponent m) := by
  letI : Module.Finite R'
      (completedFiniteBaseChange (R := R) (R' := R') (C := C)) :=
    Module.Finite.base_change R R' C
  exact
    (completedChosenComponentAlgHom
      (R := R) (R' := R') (C := C) (K := K) (L := L)
      (K' := K') m).codRestrict
        (integralClosure R' (GenericTensorFieldComponent m)) fun x ↦
      (IsIntegral.of_finite R' x).map
        (completedChosenComponentAlgHom
          (R := R) (R' := R') (C := C) (K := K) (L := L)
          (K' := K') m)

/-- For the component fixed by `Q`, the map to the component field has
kernel exactly the generic prime previously selected below the completed
closed prime. -/
theorem completedChosenComponentAlgHom_ker
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R')))
    (Q : Ideal C) [Q.IsMaximal]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    let m := completedGenericTensorChosenIdeal
      (R := R) (R' := R') (K := K) (L := L) (K' := K')
      hmax hres Q
    letI : m.IsMaximal := completedGenericTensorChosenIdeal_isMaximal
      (R := R) (R' := R') (K := K) (L := L) (K' := K')
      hmax hres Q
    RingHom.ker
      (completedChosenComponentAlgHom
        (R := R) (R' := R') (C := C) (K := K) (L := L)
        (K' := K') m).toRingHom =
      completedBaseChangeChosenGenericPrime
        (R := R) (R' := R') hmax hres Q := by
  let m := completedGenericTensorChosenIdeal
    (R := R) (R' := R') (K := K) (L := L) (K' := K')
    hmax hres Q
  let : m.IsMaximal := completedGenericTensorChosenIdeal_isMaximal
    (R := R) (R' := R') (K := K) (L := L) (K' := K')
    hmax hres Q
  let U := completedFiniteBaseChange (R := R) (R' := R') (C := C)
  let G := completedFiniteBaseChangeGenericFiber
    (R := R) (R' := R') (C := C) (K' := K')
  let : Algebra U G := Algebra.TensorProduct.rightAlgebra
  let e := completedGenericFiberEquiv
    (R := R) (R' := R') (C := C) (K := K) (L := L) (K' := K')
  ext x
  change Ideal.Quotient.mk m (e (algebraMap U G x)) = 0 ↔
    x ∈ completedBaseChangeChosenGenericPrime
      (R := R) (R' := R') hmax hres Q
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change x ∈ (m.comap e.toRingEquiv.toRingHom).comap
      (algebraMap U G) ↔ _
  rw [completedGenericTensorChosenIdeal_comap
    (R := R) (R' := R') (C := C) (K := K) (L := L) (K' := K')
    hmax hres Q]
  rw [completedBaseChangeChosenGenericIdeal_comap
    (R := R) (R' := R') (K' := K') hmax hres Q]

/-- Passing from the chosen component field to its normalization does not
change the kernel of the finite-model map. -/
theorem completedChosenNormalizationAlgHom_ker
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R')))
    (Q : Ideal C) [Q.IsMaximal]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    let m := completedGenericTensorChosenIdeal
      (R := R) (R' := R') (K := K) (L := L) (K' := K')
      hmax hres Q
    letI : m.IsMaximal := completedGenericTensorChosenIdeal_isMaximal
      (R := R) (R' := R') (K := K) (L := L) (K' := K')
      hmax hres Q
    RingHom.ker
      (completedChosenNormalizationAlgHom
        (R := R) (R' := R') (C := C) (K := K) (L := L)
        (K' := K') m).toRingHom =
      completedBaseChangeChosenGenericPrime
        (R := R) (R' := R') hmax hres Q := by
  let m := completedGenericTensorChosenIdeal
    (R := R) (R' := R') (K := K) (L := L) (K' := K')
    hmax hres Q
  let : m.IsMaximal := completedGenericTensorChosenIdeal_isMaximal
    (R := R) (R' := R') (K := K) (L := L) (K' := K')
    hmax hres Q
  let j := completedChosenNormalizationAlgHom
    (R := R) (R' := R') (C := C) (K := K) (L := L)
    (K' := K') m
  dsimp only
  change RingHom.ker j.toRingHom =
    completedBaseChangeChosenGenericPrime
      (R := R) (R' := R') hmax hres Q
  rw [← RingHom.ker_comp_of_injective j.toRingHom
    (f := (integralClosure R'
      (GenericTensorFieldComponent m)).val.toRingHom)
    Subtype.val_injective]
  change RingHom.ker
      (completedChosenComponentAlgHom
        (R := R) (R' := R') (C := C) (K := K) (L := L)
        (K' := K') m).toRingHom =
    completedBaseChangeChosenGenericPrime
      (R := R) (R' := R') hmax hres Q
  exact completedChosenComponentAlgHom_ker
    (R := R) (R' := R') (C := C) (K := K) (L := L) (K' := K')
    hmax hres Q

/-- The normalization of the `Q`-selected field component has a maximal
ideal lying over the completed closed prime selected by `Q`.  The kernel
calculation supplies the compatibility needed for integral going-up. -/
theorem exists_completedChosenNormalizationPrime
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R')))
    (Q : Ideal C) [Q.IsMaximal]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    let U := completedFiniteBaseChange (R := R) (R' := R') (C := C)
    let P := completedBaseChangeChosenPrime (R := R) (R' := R') Q
    let m := completedGenericTensorChosenIdeal
      (R := R) (R' := R') (K := K) (L := L) (K' := K')
      hmax hres Q
    letI : m.IsMaximal := completedGenericTensorChosenIdeal_isMaximal
      (R := R) (R' := R') (K := K) (L := L) (K' := K')
      hmax hres Q
    let j := completedChosenNormalizationAlgHom
      (R := R) (R' := R') (C := C) (K := K) (L := L)
      (K' := K') m
    letI : Algebra U
        (integralClosure R' (GenericTensorFieldComponent m)) :=
      j.toAlgebra
    ∃ q : Ideal (integralClosure R' (GenericTensorFieldComponent m)),
      q.IsMaximal ∧ q.LiesOver P := by
  let U := completedFiniteBaseChange (R := R) (R' := R') (C := C)
  let P := completedBaseChangeChosenPrime (R := R) (R' := R') Q
  let m := completedGenericTensorChosenIdeal
    (R := R) (R' := R') (K := K) (L := L) (K' := K')
    hmax hres Q
  let : m.IsMaximal := completedGenericTensorChosenIdeal_isMaximal
    (R := R) (R' := R') (K := K) (L := L) (K' := K')
    hmax hres Q
  let IC := integralClosure R' (GenericTensorFieldComponent m)
  let j := completedChosenNormalizationAlgHom
    (R := R) (R' := R') (C := C) (K := K) (L := L)
    (K' := K') m
  let : Algebra U IC := j.toAlgebra
  let : IsScalarTower R' U IC :=
    IsScalarTower.of_algebraMap_eq fun x => j.commutes x |>.symm
  let : Algebra.IsIntegral R' IC :=
    IsIntegralClosure.isIntegral_algebra R'
      (GenericTensorFieldComponent m)
  let : Algebra.IsIntegral U IC :=
    Algebra.IsIntegral.tower_top R'
  have hgeom := completedBaseChangeChosenPrime_isMaximal_liesOver
    (R := R) (R' := R') hmax hres Q
  let : P.IsMaximal := hgeom.1
  have hk : RingHom.ker (algebraMap U IC) ≤ P := by
    change RingHom.ker j.toRingHom ≤ P
    rw [completedChosenNormalizationAlgHom_ker
      (R := R) (R' := R') (C := C) (K := K) (L := L) (K' := K')
      hmax hres Q]
    exact (completedBaseChangeChosenGenericPrime_spec
      (R := R) (R' := R') hmax hres Q).1
  obtain ⟨q, hqmax, hqcomap⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral P hk
  exact ⟨q, hqmax, (Ideal.liesOver_iff q P).mpr hqcomap.symm⟩

end EtaleFundamentalGroups

end
