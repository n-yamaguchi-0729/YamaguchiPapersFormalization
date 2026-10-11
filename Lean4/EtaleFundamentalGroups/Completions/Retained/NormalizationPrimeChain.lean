/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Completions.Retained.PrimeChain
import EtaleFundamentalGroups.Completions.Chosen.NormalizationPrime
import EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product

/-!
# Normalization primes in a retained completed component

A generic/height-one/closed prime chain in the completed finite model fixes a
literal component of the completed generic tensor product.  This file maps
the finite model into that component and then into its normalization.  The
kernel is the supplied generic prime.  Integral going-up therefore lifts the
remaining two primes to a height-one/closed chain in the normalization of
the *same* component.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uR' uS uK uL uK'

variable {R : Type uR} {R' : Type uR'} {S : Type uS}
variable [CommRing R] [IsDomain R]
variable [CommRing R'] [IsDomain R'] [Algebra R R']
variable [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
variable {K' : Type uK'} [Field K'] [Algebra R' K']
variable [IsFractionRing R' K']
variable {K : Type uK} {L : Type uL}
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra S L] [IsFractionRing S L]
variable [Algebra R L] [IsScalarTower R S L]
variable [Algebra K L] [IsScalarTower R K L]
variable [Algebra R K'] [IsScalarTower R R' K']
variable [Algebra K K'] [IsScalarTower R K K']

/-- Map the completed finite model to the literal generic tensor component
selected by a supplied generic prime. -/
noncomputable def retainedCompletedChosenComponentAlgHom
    (N : Ideal (R' ⊗[R] S)) [N.IsPrime]
    [N.LiesOver (⊥ : Ideal R')] :
    let m := retainedCompletedGenericTensorIdeal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    letI : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    let M := GenericTensorFieldComponent m
    letI : Algebra R' M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := R') m
    (R' ⊗[R] S) →ₐ[R'] M := by
  dsimp only
  let m := retainedCompletedGenericTensorIdeal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  letI : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
  let M := GenericTensorFieldComponent m
  let r'MAlgebra : Algebra R' M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := R') m
  letI : Algebra R' M := r'MAlgebra
  letI : SMul R' M := r'MAlgebra.toSMul
  letI : IsScalarTower R' K' M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact
    ((Ideal.Quotient.mkₐ K' m).restrictScalars R').comp
      ((AlgHom.restrictScalars R'
        (retainedCompletedGenericFiberEquiv
          (R := R) (R' := R') (S := S) (K := K) (L := L)
          (K' := K')).toAlgHom).comp
        (Algebra.TensorProduct.includeRight :
          (R' ⊗[R] S) →ₐ[R']
            retainedCompletedFiniteBaseChangeGenericFiber
              (R := R) (R' := R') (S := S) (K' := K')))

/-- Restrict the retained component map to the normalization over the new
base. -/
noncomputable def retainedCompletedChosenNormalizationAlgHom
    (N : Ideal (R' ⊗[R] S)) [N.IsPrime]
    [N.LiesOver (⊥ : Ideal R')] :
    let m := retainedCompletedGenericTensorIdeal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    letI : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    let M := GenericTensorFieldComponent m
    letI : Algebra R' M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := R') m
    (R' ⊗[R] S) →ₐ[R'] integralClosure R' M := by
  dsimp only
  let m := retainedCompletedGenericTensorIdeal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  letI : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
  let M := GenericTensorFieldComponent m
  let r'MAlgebra : Algebra R' M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := R') m
  letI : Algebra R' M := r'MAlgebra
  letI : SMul R' M := r'MAlgebra.toSMul
  letI : IsScalarTower R' K' M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : IsScalarTower R' R' M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ by simp
  letI : Module.Finite R' (R' ⊗[R] S) :=
    Module.Finite.base_change R R' S
  exact
    (retainedCompletedChosenComponentAlgHom
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N).codRestrict
        (integralClosure R' M) fun x ↦
      (IsIntegral.of_finite R' x).map
        (retainedCompletedChosenComponentAlgHom
          (R := R) (R' := R') (S := S) (K := K) (L := L)
          (K' := K') N)

/-- The retained finite-model map has exactly the supplied generic prime as
its kernel. -/
theorem retainedCompletedChosenComponentAlgHom_ker
    (N : Ideal (R' ⊗[R] S)) [N.IsPrime]
    [N.LiesOver (⊥ : Ideal R')] :
    let m := retainedCompletedGenericTensorIdeal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    letI : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    let M := GenericTensorFieldComponent m
    letI : Algebra R' M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := R') m
    RingHom.ker
        (retainedCompletedChosenComponentAlgHom
          (R := R) (R' := R') (S := S) (K := K) (L := L)
          (K' := K') N).toRingHom = N := by
  let T := R' ⊗[R] S
  let G₀ := retainedCompletedFiniteBaseChangeGenericFiber
    (R := R) (R' := R') (S := S) (K' := K')
  let e := retainedCompletedGenericFiberEquiv
    (R := R) (R' := R') (S := S) (K := K) (L := L) (K' := K')
  let n₀ := retainedCompletedGenericIdeal
    (R := R) (R' := R') (S := S) (K' := K') N
  let m := retainedCompletedGenericTensorIdeal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
  let M := GenericTensorFieldComponent m
  let r'MAlgebra : Algebra R' M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := R') m
  let : Algebra R' M := r'MAlgebra
  let : SMul R' M := r'MAlgebra.toSMul
  let : IsScalarTower R' K' M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra T G₀ := Algebra.TensorProduct.rightAlgebra
  let M : Submonoid T :=
    Algebra.algebraMapSubmonoid T (nonZeroDivisors R')
  let : IsLocalization M G₀ :=
    IsLocalization.tensorRight (R := R') (S := T) (A := K')
      (nonZeroDivisors R')
  have hdisjoint : Disjoint (M : Set T) (N : Set T) :=
    retainedCompletedGenericPrime_disjoint
      (R := R) (R' := R') (S := S) N
  have hn₀Comap : n₀.comap (algebraMap T G₀) = N :=
    IsLocalization.under_map_of_isPrime_disjoint
      M G₀ (inferInstance : N.IsPrime) hdisjoint
  have hmComap : m.comap e.toRingEquiv.toRingHom = n₀ := by
    exact Ideal.comap_map_of_bijective
      e.toRingEquiv.toRingHom e.toRingEquiv.bijective
  ext x
  change Ideal.Quotient.mk m (e (algebraMap T G₀ x)) = 0 ↔ x ∈ N
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change x ∈ (m.comap e.toRingEquiv.toRingHom).comap
      (algebraMap T G₀) ↔ x ∈ N
  rw [hmComap, hn₀Comap]

/-- Passing from the retained component field to its normalization does not
change the finite-model kernel. -/
theorem retainedCompletedChosenNormalizationAlgHom_ker
    (N : Ideal (R' ⊗[R] S)) [N.IsPrime]
    [N.LiesOver (⊥ : Ideal R')] :
    let m := retainedCompletedGenericTensorIdeal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    letI : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    let M := GenericTensorFieldComponent m
    letI : Algebra R' M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := R') m
    RingHom.ker
        (retainedCompletedChosenNormalizationAlgHom
          (R := R) (R' := R') (S := S) (K := K) (L := L)
          (K' := K') N).toRingHom = N := by
  let m := retainedCompletedGenericTensorIdeal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
  let M := GenericTensorFieldComponent m
  let r'MAlgebra : Algebra R' M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := R') m
  let : Algebra R' M := r'MAlgebra
  let : SMul R' M := r'MAlgebra.toSMul
  let : IsScalarTower R' K' M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let j := retainedCompletedChosenNormalizationAlgHom
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  change RingHom.ker j.toRingHom = N
  rw [← RingHom.ker_comp_of_injective j.toRingHom
    (f := (integralClosure R' M).val.toRingHom)
    Subtype.val_injective]
  change RingHom.ker
      (retainedCompletedChosenComponentAlgHom
        (R := R) (R' := R') (S := S) (K := K) (L := L)
        (K' := K') N).toRingHom = N
  exact retainedCompletedChosenComponentAlgHom_ker
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N

/-- The proposition that a retained finite-model chain lifts to the
normalization of its selected literal generic tensor component. -/
def HasRetainedCompletedNormalizationPrimeChain
    (N Q P : Ideal (R' ⊗[R] S))
    [N.IsPrime] [N.LiesOver (⊥ : Ideal R')]
    [Q.IsPrime] [P.IsMaximal] : Prop :=
    let m := retainedCompletedGenericTensorIdeal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    letI : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    let M := GenericTensorFieldComponent m
    letI : Algebra R' M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := R') m
    let IC := integralClosure R' M
    let j := retainedCompletedChosenNormalizationAlgHom
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    letI : Algebra (R' ⊗[R] S) IC := j.toAlgebra
    ∃ q p : Ideal IC,
      q ≤ p ∧ q.IsPrime ∧ q.LiesOver Q ∧
        p.IsMaximal ∧ p.LiesOver P

/-- A retained generic/height-one/closed chain in the completed finite model
lifts to a height-one/closed chain in the normalization of the same literal
generic tensor component. -/
theorem exists_retainedCompletedNormalizationPrimeChain
    (N Q P : Ideal (R' ⊗[R] S))
    [N.IsPrime] [N.LiesOver (⊥ : Ideal R')]
    [Q.IsPrime] [P.IsMaximal]
    (hNQ : N ≤ Q) (hQP : Q ≤ P) :
    HasRetainedCompletedNormalizationPrimeChain
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N Q P := by
  unfold HasRetainedCompletedNormalizationPrimeChain
  dsimp only
  let T := R' ⊗[R] S
  let m := retainedCompletedGenericTensorIdeal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
  let M := GenericTensorFieldComponent m
  let r'MAlgebra : Algebra R' M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := R') m
  let : Algebra R' M := r'MAlgebra
  let : SMul R' M := r'MAlgebra.toSMul
  let : IsScalarTower R' K' M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let IC := integralClosure R' M
  let j := retainedCompletedChosenNormalizationAlgHom
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let : Algebra T IC := j.toAlgebra
  let : IsScalarTower R' T IC :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (j.commutes x).symm
  let : Algebra.IsIntegral R' IC :=
    IsIntegralClosure.isIntegral_algebra R' M
  let : Algebra.IsIntegral T IC := Algebra.IsIntegral.tower_top R'
  have hkerQ : RingHom.ker (algebraMap T IC) ≤ Q := by
    change RingHom.ker j.toRingHom ≤ Q
    rw [retainedCompletedChosenNormalizationAlgHom_ker
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N]
    exact hNQ
  obtain ⟨q, -, hqPrime, hqComap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral Q (⊥ : Ideal IC) hkerQ
  let : q.IsPrime := hqPrime
  have hqOver : q.LiesOver Q :=
    (Ideal.liesOver_iff q Q).mpr hqComap.symm
  have hqP : q.comap (algebraMap T IC) ≤ P := by
    change q.under T ≤ P
    rw [hqComap]
    exact hQP
  obtain ⟨p, hqp, hpPrime, hpComap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime P q hqP
  let : p.IsPrime := hpPrime
  have hpMax : p.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under
      (R := T) (S := IC) p (hpComap.symm ▸ (inferInstance : P.IsMaximal))
  exact ⟨q, p, hqp, hqPrime, hqOver, hpMax,
    (Ideal.liesOver_iff p P).mpr hpComap.symm⟩

end EtaleFundamentalGroups

end
