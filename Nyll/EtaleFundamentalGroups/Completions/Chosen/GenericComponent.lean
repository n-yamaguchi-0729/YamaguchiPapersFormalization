/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Nyll.EtaleFundamentalGroups.Completions.FiniteEtale.ClosedPrime
import Nyll.EtaleFundamentalGroups.Completions.Tensor.Ramification
import Nyll.EtaleFundamentalGroups.FiniteEtale.BaseChange.GenericFiber
import Nyll.SchemeTheory.RingTheory.GenericFiber.Finite
import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.Basic

/-!
# A completed generic component selected by a closed prime

Let `C / R` be a finite extension of domains, with `R` a DVR, and let `Q`
be a maximal ideal of `C` above the closed point.  For a faithfully flat
local base change `R → R'` which preserves the closed point and residue
field, the extension of `Q` to `R' ⊗[R] C` is a maximal ideal `P`; it
contracts to exactly `Q` and has the same ramification index.

Flat going-down selects a generic prime below this specified `P`.  After
inverting the nonzero elements of `R'`, it becomes a maximal ideal of the
completed generic fibre.  The resulting field component is therefore fixed
once from `Q`, rather than being replaced by an unrelated tensor component.
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

/-- The finite model after the completed base change. -/
abbrev completedFiniteBaseChange := R' ⊗[R] C

/-- The closed prime in the finite completed model selected by `Q`. -/
noncomputable def completedBaseChangeChosenPrime
    (Q : Ideal C) : Ideal (completedFiniteBaseChange
      (R := R) (R' := R') (C := C)) := by
  let U := completedFiniteBaseChange (R := R) (R' := R') (C := C)
  letI : Algebra C U := Algebra.TensorProduct.rightAlgebra
  exact Q.map (algebraMap C U)

omit [IsDomain R'] [IsDomain C] [Module.Finite R C]
  [FaithfulSMul R C] in
/-- Closed-point and residue-field preservation make the extension of `Q`
a maximal ideal over the closed point of `R'`. -/
theorem completedBaseChangeChosenPrime_isMaximal_liesOver
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R')))
    (Q : Ideal C) [Q.IsMaximal]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    let P := completedBaseChangeChosenPrime
      (R := R) (R' := R') Q
    P.IsMaximal ∧ P.LiesOver (IsLocalRing.maximalIdeal R') := by
  simpa [completedBaseChangeChosenPrime, completedFiniteBaseChange] using
    (tensorProduct_map_liesOver_maximalIdeal_of_residueFieldMap_bijective
      (R := R) (R' := R') Q hmax hres)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain R']
  [IsLocalRing R'] [IsLocalHom (algebraMap R R')] [IsDomain C]
  [Module.Finite R C] [FaithfulSMul R C] in
/-- The selected completed closed prime contracts to the specified `Q`. -/
theorem completedBaseChangeChosenPrime_comap_right
    (Q : Ideal C) :
    let U := completedFiniteBaseChange (R := R) (R' := R') (C := C)
    letI : Algebra C U := Algebra.TensorProduct.rightAlgebra
    (completedBaseChangeChosenPrime (R := R) (R' := R') Q).comap
        (algebraMap C U) = Q := by
  let U := completedFiniteBaseChange (R := R) (R' := R') (C := C)
  let : Algebra C U := Algebra.TensorProduct.rightAlgebra
  let : Module.FaithfullyFlat C U :=
    Module.FaithfullyFlat.of_linearEquiv
      (R := C) (M := C ⊗[R] R')
      (Algebra.TensorProduct.commRight R C R').symm.toLinearEquiv
  simpa only [completedBaseChangeChosenPrime] using
    (Ideal.comap_map_eq_self_of_faithfullyFlat (B := U) Q)

omit [IsDomain R'] in
/-- Ramification at the selected completed closed prime is exactly the
ramification at the original `Q`. -/
theorem completedBaseChangeChosenPrime_ramificationIdx_eq
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R')))
    (Q : Ideal C) [Q.IsMaximal]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    (completedBaseChangeChosenPrime (R := R) (R' := R') Q).ramificationIdx R' =
      Q.ramificationIdx R := by
  let U := completedFiniteBaseChange (R := R) (R' := R') (C := C)
  let P := completedBaseChangeChosenPrime (R := R) (R' := R') Q
  let : Algebra C U := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R C U :=
    Algebra.TensorProduct.right_isScalarTower
  let : Module.FaithfullyFlat C U :=
    Module.FaithfullyFlat.of_linearEquiv
      (R := C) (M := C ⊗[R] R')
      (Algebra.TensorProduct.commRight R C R').symm.toLinearEquiv
  let : Module.Flat R C := inferInstance
  let : Module.Flat R' U := Module.Flat.baseChange R R' C
  have hgeom := completedBaseChangeChosenPrime_isMaximal_liesOver
    (R := R) (R' := R') hmax hres Q
  let : P.IsPrime := hgeom.1.isPrime
  let : P.LiesOver (IsLocalRing.maximalIdeal R') := hgeom.2
  exact ramificationIdx_eq_of_flat_baseChange_mapped_primes
    (IsLocalRing.maximalIdeal R) Q
    (IsLocalRing.maximalIdeal R') P hmax rfl

/-- A generic prime of the finite base change lying below the closed prime
selected by `Q`. -/
theorem exists_completedBaseChangeChosenGenericPrime
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R')))
    (Q : Ideal C) [Q.IsMaximal]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    let U := completedFiniteBaseChange (R := R) (R' := R') (C := C)
    let P := completedBaseChangeChosenPrime (R := R) (R' := R') Q
    ∃ N : Ideal U, N ≤ P ∧ N.IsPrime ∧ N.LiesOver (⊥ : Ideal R') := by
  let U := completedFiniteBaseChange (R := R) (R' := R') (C := C)
  let P := completedBaseChangeChosenPrime (R := R) (R' := R') Q
  let : Module.Flat R C := inferInstance
  let : Module.Flat R' U := Module.Flat.baseChange R R' C
  have hgeom := completedBaseChangeChosenPrime_isMaximal_liesOver
    (R := R) (R' := R') hmax hres Q
  let : P.IsPrime := hgeom.1.isPrime
  let : P.LiesOver (IsLocalRing.maximalIdeal R') := hgeom.2
  obtain ⟨N, hNP, hNprime, hNover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le
      (R := R') (S := U) (p := (⊥ : Ideal R'))
      (q := IsLocalRing.maximalIdeal R') P bot_le
  exact ⟨N, hNP, hNprime, hNover⟩

/-- The fixed generic prime below the completed closed point selected by
`Q`. -/
noncomputable def completedBaseChangeChosenGenericPrime
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R')))
    (Q : Ideal C) [Q.IsMaximal]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    Ideal (completedFiniteBaseChange (R := R) (R' := R') (C := C)) :=
  Classical.choose (exists_completedBaseChangeChosenGenericPrime
    (R := R) (R' := R') hmax hres Q)

theorem completedBaseChangeChosenGenericPrime_spec
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R')))
    (Q : Ideal C) [Q.IsMaximal]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    let P := completedBaseChangeChosenPrime (R := R) (R' := R') Q
    let N := completedBaseChangeChosenGenericPrime
      (R := R) (R' := R') hmax hres Q
    N ≤ P ∧ N.IsPrime ∧ N.LiesOver (⊥ : Ideal R') :=
  Classical.choose_spec (exists_completedBaseChangeChosenGenericPrime
    (R := R) (R' := R') hmax hres Q)

section GenericFibre

variable {K' : Type uK'} [Field K'] [Algebra R' K']
variable [IsFractionRing R' K']

/-- The generic fibre of the finite completed model. -/
abbrev completedFiniteBaseChangeGenericFiber :=
  K' ⊗[R'] completedFiniteBaseChange (R := R) (R' := R') (C := C)

/-- Extend the fixed generic prime below `P` to the completed generic
fibre. -/
noncomputable def completedBaseChangeChosenGenericIdeal
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R')))
    (Q : Ideal C) [Q.IsMaximal]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    Ideal (completedFiniteBaseChangeGenericFiber
      (R := R) (R' := R') (C := C) (K' := K')) := by
  let U := completedFiniteBaseChange (R := R) (R' := R') (C := C)
  let G := completedFiniteBaseChangeGenericFiber
    (R := R) (R' := R') (C := C) (K' := K')
  letI : Algebra U G := Algebra.TensorProduct.rightAlgebra
  exact (completedBaseChangeChosenGenericPrime
    (R := R) (R' := R') hmax hres Q).map (algebraMap U G)

private theorem completedBaseChangeChosenGenericPrime_disjoint
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R')))
    (Q : Ideal C) [Q.IsMaximal]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    let U := completedFiniteBaseChange (R := R) (R' := R') (C := C)
    Disjoint
      (Algebra.algebraMapSubmonoid U (nonZeroDivisors R') : Set U)
      (completedBaseChangeChosenGenericPrime
        (R := R) (R' := R') hmax hres Q : Set U) := by
  let U := completedFiniteBaseChange (R := R) (R' := R') (C := C)
  let N := completedBaseChangeChosenGenericPrime
    (R := R) (R' := R') hmax hres Q
  have hN := completedBaseChangeChosenGenericPrime_spec
    (R := R) (R' := R') hmax hres Q
  let : N.IsPrime := hN.2.1
  let : N.LiesOver (⊥ : Ideal R') := hN.2.2
  rw [Set.disjoint_left]
  intro x hxM hxN
  rcases hxM with ⟨r, hr, rfl⟩
  have hrN : r ∈ N.under R' := hxN
  have hr0 : r = 0 := by
    have : r ∈ (⊥ : Ideal R') := by
      rw [N.over_def (⊥ : Ideal R')]
      exact hrN
    simpa only [Ideal.mem_bot] using this
  exact (nonZeroDivisors.coe_ne_zero ⟨r, hr⟩) hr0

theorem completedBaseChangeChosenGenericIdeal_isMaximal
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R')))
    (Q : Ideal C) [Q.IsMaximal]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    (completedBaseChangeChosenGenericIdeal
      (R := R) (R' := R') (K' := K') hmax hres Q).IsMaximal := by
  let U := completedFiniteBaseChange (R := R) (R' := R') (C := C)
  let G := completedFiniteBaseChangeGenericFiber
    (R := R) (R' := R') (C := C) (K' := K')
  let N := completedBaseChangeChosenGenericPrime
    (R := R) (R' := R') hmax hres Q
  let m := completedBaseChangeChosenGenericIdeal
    (R := R) (R' := R') (K' := K') hmax hres Q
  let : Algebra U G := Algebra.TensorProduct.rightAlgebra
  let : IsLocalization
      (Algebra.algebraMapSubmonoid U (nonZeroDivisors R')) G :=
    IsLocalization.tensorRight (R := R') (S := U) (A := K')
      (nonZeroDivisors R')
  have hN := completedBaseChangeChosenGenericPrime_spec
    (R := R) (R' := R') hmax hres Q
  let : N.IsPrime := hN.2.1
  have hmprime : m.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid U (nonZeroDivisors R')) G N
      inferInstance
      (completedBaseChangeChosenGenericPrime_disjoint
        (R := R) (R' := R') hmax hres Q)
  let : m.IsPrime := hmprime
  let : Module.Finite R' U := Module.Finite.base_change R R' C
  let : Module.Finite K' G := Module.Finite.base_change R' K' U
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := K') m
  have hcomapPrime :
      (m.comap (algebraMap K' G)).IsPrime := hmprime.comap _
  let : (m.comap (algebraMap K' G)).IsPrime := hcomapPrime
  change (m.comap (algebraMap K' G)).IsMaximal
  rw [Ideal.eq_bot_of_prime (m.comap (algebraMap K' G))]
  exact Ideal.bot_isMaximal

/-- Contracting the completed generic ideal recovers the fixed generic prime
below the `Q`-selected closed point. -/
theorem completedBaseChangeChosenGenericIdeal_comap
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R')))
    (Q : Ideal C) [Q.IsMaximal]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    let U := completedFiniteBaseChange (R := R) (R' := R') (C := C)
    let G := completedFiniteBaseChangeGenericFiber
      (R := R) (R' := R') (C := C) (K' := K')
    letI : Algebra U G := Algebra.TensorProduct.rightAlgebra
    (completedBaseChangeChosenGenericIdeal
        (R := R) (R' := R') (K' := K') hmax hres Q).comap
        (algebraMap U G) =
      completedBaseChangeChosenGenericPrime
        (R := R) (R' := R') hmax hres Q := by
  let U := completedFiniteBaseChange (R := R) (R' := R') (C := C)
  let G := completedFiniteBaseChangeGenericFiber
    (R := R) (R' := R') (C := C) (K' := K')
  let N := completedBaseChangeChosenGenericPrime
    (R := R) (R' := R') hmax hres Q
  let : Algebra U G := Algebra.TensorProduct.rightAlgebra
  let : IsLocalization
      (Algebra.algebraMapSubmonoid U (nonZeroDivisors R')) G :=
    IsLocalization.tensorRight (R := R') (S := U) (A := K')
      (nonZeroDivisors R')
  have hN := completedBaseChangeChosenGenericPrime_spec
    (R := R) (R' := R') hmax hres Q
  exact IsLocalization.under_map_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid U (nonZeroDivisors R')) G
    hN.2.1
    (completedBaseChangeChosenGenericPrime_disjoint
      (R := R) (R' := R') hmax hres Q)

section OriginalGenericTensor

variable {K : Type uK} {L : Type uL}
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra C L] [IsFractionRing C L]
variable [Algebra R L] [IsScalarTower R C L]
variable [Algebra K L] [IsScalarTower R K L]
variable [Algebra R K'] [IsScalarTower R R' K']
variable [Algebra K K'] [IsScalarTower R K K']

/-- Reassociate the completed generic fibre with the usual field tensor
`K' ⊗[K] L`. -/
noncomputable def completedGenericFiberEquiv :
    completedFiniteBaseChangeGenericFiber
        (R := R) (R' := R') (C := C) (K' := K') ≃ₐ[K']
      (K' ⊗[K] L) := by
  let U := completedFiniteBaseChange (R := R) (R' := R') (C := C)
  letI : Algebra K' (U ⊗[R'] K') :=
    Algebra.TensorProduct.rightAlgebra
  let eBase :
      (K' ⊗[R'] U) ≃ₐ[K'] (K' ⊗[R] C) :=
    (Algebra.TensorProduct.commRight R' K' U).trans
      (baseChangeGenericFiberEquiv R R' C K')
  let eGeneric : (K ⊗[R] C) ≃ₐ[K] L :=
    finiteGenericFiberAlgEquiv
      (R := R) (C := C) (K := K) (E := L)
  exact eBase.trans
    (iteratedGenericFiberEquiv R K K' C L eGeneric)

/-- The maximal ideal of `K' ⊗[K] L` obtained from the generic prime below
the completed closed point selected by `Q`. -/
noncomputable def completedGenericTensorChosenIdeal
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R')))
    (Q : Ideal C) [Q.IsMaximal]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    Ideal (K' ⊗[K] L) :=
  (completedBaseChangeChosenGenericIdeal
      (R := R) (R' := R') (K' := K') hmax hres Q).map
    (completedGenericFiberEquiv
      (R := R) (R' := R') (C := C) (K := K) (L := L)
      (K' := K')).toRingEquiv.toRingHom

theorem completedGenericTensorChosenIdeal_isMaximal
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R')))
    (Q : Ideal C) [Q.IsMaximal]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    (completedGenericTensorChosenIdeal
      (R := R) (R' := R') (K := K) (L := L) (K' := K')
      hmax hres Q).IsMaximal := by
  let e := completedGenericFiberEquiv
    (R := R) (R' := R') (C := C) (K := K) (L := L) (K' := K')
  have hm := completedBaseChangeChosenGenericIdeal_isMaximal
    (R := R) (R' := R') (K' := K') hmax hres Q
  exact hm.map_bijective (f := e.toRingEquiv.toRingHom)
    e.toRingEquiv.bijective

omit [IsFractionRing R' K'] in
/-- Under the canonical reassociation, the selected tensor component is
exactly the generic ideal already fixed below the completed closed prime. -/
theorem completedGenericTensorChosenIdeal_comap
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R')))
    (Q : Ideal C) [Q.IsMaximal]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    let e := completedGenericFiberEquiv
      (R := R) (R' := R') (C := C) (K := K) (L := L) (K' := K')
    let m := completedBaseChangeChosenGenericIdeal
      (R := R) (R' := R') (K' := K') hmax hres Q
    (completedGenericTensorChosenIdeal
        (R := R) (R' := R') (K := K) (L := L) (K' := K')
        hmax hres Q).comap e.toRingEquiv.toRingHom = m := by
  dsimp only [completedGenericTensorChosenIdeal]
  exact Ideal.comap_map_of_bijective
    (f := (completedGenericFiberEquiv
      (R := R) (R' := R') (C := C) (K := K) (L := L)
      (K' := K')).toRingEquiv.toRingHom)
    (completedGenericFiberEquiv
      (R := R) (R' := R') (C := C) (K := K) (L := L) (K' := K')).bijective

end OriginalGenericTensor

end GenericFibre

end EtaleFundamentalGroups

end
