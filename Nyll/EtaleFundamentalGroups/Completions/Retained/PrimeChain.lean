/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.GoingDown
import Nyll.EtaleFundamentalGroups.Completions.Chosen.GenericComponent
import Nyll.EtaleFundamentalGroups.Completions.FiniteEtale.ClosedPrime

/-!
# Retaining a prime chain under completion base change

Let `q ≤ p` be a prime and a closed prime in a finite model over a local
base.  A closed-point-preserving faithfully flat base change sends `p` to a
specified maximal ideal `P` of the tensor product.  Flat going-down then
selects a prime `Q ≤ P` over the *specified* `q`.  If the finite model is
flat over the base, a second going-down step selects a generic prime below
that same `Q`.

The point of the construction is that neither the height-one branch nor the
closed factor is reselected after completion.  The resulting chain is the
finite-model input for selecting one literal completed generic component.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uR' uS uK uL uK'

/-- A specified chain `q ≤ p` survives a closed-point-preserving faithfully
flat base change inside the tensor factor selected by `p`.

The upper prime is produced by flat going-down from the literal extension of
`p`; in particular it contracts to the supplied `q`, rather than merely to
some prime below `p`. -/
theorem exists_tensorProduct_prime_le_retainedClosedPrime
    {R : Type uR} {R' : Type uR'} {S : Type uS}
    [CommRing R] [CommRing R'] [CommRing S]
    [IsLocalRing R] [IsLocalRing R']
    [Algebra R R'] [Algebra R S]
    [IsLocalHom (algebraMap R R')]
    [Module.FaithfullyFlat R R']
    (q p : Ideal S) [q.IsPrime] [p.IsMaximal]
    [p.LiesOver (IsLocalRing.maximalIdeal R)]
    (hqp : q ≤ p)
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R'))) :
    let T := R' ⊗[R] S
    letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
    let P := p.map (algebraMap S T)
    ∃ Q : Ideal T,
      Q ≤ P ∧ Q.IsPrime ∧ Q.LiesOver q ∧
        P.IsMaximal ∧ P.LiesOver (IsLocalRing.maximalIdeal R') := by
  dsimp only
  let T := R' ⊗[R] S
  let : Algebra S T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R S T :=
    Algebra.TensorProduct.right_isScalarTower
  let : Module.FaithfullyFlat S T :=
    Module.FaithfullyFlat.of_linearEquiv
      (R := S) (M := S ⊗[R] R')
      (Algebra.TensorProduct.commRight R S R').symm.toLinearEquiv
  let P := p.map (algebraMap S T)
  have hPGeometry :=
    tensorProduct_map_liesOver_maximalIdeal_of_residueFieldMap_bijective
      (R := R) (R' := R') p hmax hres
  let : P.IsPrime := hPGeometry.1.isPrime
  let : P.LiesOver p := by
    exact
      Ideal.LiesOver.mk
        (Ideal.comap_map_eq_self_of_faithfullyFlat
          (B := T) p).symm
  obtain ⟨Q, hQP, hQPrime, hQOver⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le
      (R := S) (S := T) (p := q) (q := p) P hqp
  exact ⟨Q, hQP, hQPrime, hQOver,
    hPGeometry.1, hPGeometry.2⟩

/-- If the finite model is flat over the original base, the retained
height-one/closed chain contains a generic prime over the generic point of
the new base.  Thus all three primes belong to one literal completed finite
model component. -/
theorem exists_tensorProduct_genericPrime_le_prime_le_retainedClosedPrime
    {R : Type uR} {R' : Type uR'} {S : Type uS}
    [CommRing R] [CommRing R'] [CommRing S]
    [IsLocalRing R] [IsLocalRing R'] [IsDomain R']
    [Algebra R R'] [Algebra R S]
    [IsLocalHom (algebraMap R R')]
    [Module.FaithfullyFlat R R'] [Module.Flat R S]
    (q p : Ideal S) [q.IsPrime] [p.IsMaximal]
    [p.LiesOver (IsLocalRing.maximalIdeal R)]
    (hqp : q ≤ p)
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R'))) :
    let T := R' ⊗[R] S
    letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
    let P := p.map (algebraMap S T)
    ∃ N Q : Ideal T,
      N ≤ Q ∧ Q ≤ P ∧
        N.IsPrime ∧ N.LiesOver (⊥ : Ideal R') ∧
        Q.IsPrime ∧ Q.LiesOver q ∧
        P.IsMaximal ∧ P.LiesOver (IsLocalRing.maximalIdeal R') := by
  dsimp only
  let T := R' ⊗[R] S
  let : Algebra R' T := Algebra.TensorProduct.leftAlgebra
  let : Algebra S T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R R' T := inferInstance
  let : IsScalarTower R S T :=
    Algebra.TensorProduct.right_isScalarTower
  let : Module.Flat R' T := Module.Flat.baseChange R R' S
  obtain ⟨Q, hQP, hQPrime, hQOver, hPMax, hPOver⟩ :=
    exists_tensorProduct_prime_le_retainedClosedPrime
      (R := R) (R' := R') q p hqp hmax hres
  let : Q.IsPrime := hQPrime
  let qR' := Q.under R'
  let : qR'.IsPrime := hQPrime.comap (algebraMap R' T)
  let : Q.LiesOver qR' := Ideal.over_under (A := R') Q
  obtain ⟨N, hNQ, hNPrime, hNOver⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le
      (R := R') (S := T) (p := (⊥ : Ideal R'))
      (q := qR') Q bot_le
  exact ⟨N, Q, hNQ, hQP, hNPrime, hNOver,
    hQPrime, hQOver, hPMax, hPOver⟩

/-- Maximal-adic specialization of the retained generic/height-one/closed
prime chain.  All completion geometry is supplied by the canonical adic
completion map. -/
theorem exists_adicCompletion_genericPrime_le_prime_le_retainedClosedPrime
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R]
    [Algebra R S] [Module.Flat R S]
    (q p : Ideal S) [q.IsPrime] [p.IsMaximal]
    [p.LiesOver (IsLocalRing.maximalIdeal R)]
    (hqp : q ≤ p)
    (hcompletionDomain :
      IsDomain (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :
    let R' := AdicCompletion (IsLocalRing.maximalIdeal R) R
    let T := R' ⊗[R] S
    letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
    let P := p.map (algebraMap S T)
    ∃ N Q : Ideal T,
      N ≤ Q ∧ Q ≤ P ∧
        N.IsPrime ∧ N.LiesOver (⊥ : Ideal R') ∧
        Q.IsPrime ∧ Q.LiesOver q ∧
        P.IsMaximal ∧ P.LiesOver (IsLocalRing.maximalIdeal R') := by
  dsimp only
  let R' := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let : IsDomain R' := hcompletionDomain
  let : Module.FaithfullyFlat R R' :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact
    exists_tensorProduct_genericPrime_le_prime_le_retainedClosedPrime
      (R := R) (R' := R') q p hqp
      AdicCompletion.maximalIdeal_eq_map.symm
      (AdicCompletion.residueField_map_bijective R)

section LiteralGenericComponent

variable {R : Type uR} {R' : Type uR'} {S : Type uS}
variable [CommRing R] [IsDomain R]
variable [CommRing R'] [IsDomain R'] [Algebra R R']
variable [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
variable {K' : Type uK'} [Field K'] [Algebra R' K']
variable [IsFractionRing R' K']

/-- The generic fibre of a completed finite base change.  This variant is
parameterized by a supplied generic prime, rather than by an independently
chosen closed factor. -/
abbrev retainedCompletedFiniteBaseChangeGenericFiber :=
  K' ⊗[R'] (R' ⊗[R] S)

/-- Extend a supplied generic prime of the completed finite model to its
generic fibre. -/
noncomputable def retainedCompletedGenericIdeal
    (N : Ideal (R' ⊗[R] S)) :
    Ideal (retainedCompletedFiniteBaseChangeGenericFiber
      (R := R) (R' := R') (S := S) (K' := K')) := by
  let T := R' ⊗[R] S
  let G := retainedCompletedFiniteBaseChangeGenericFiber
    (R := R) (R' := R') (S := S) (K' := K')
  letI : Algebra T G := Algebra.TensorProduct.rightAlgebra
  exact N.map (algebraMap T G)

omit [IsDomain R] [IsDomain S] [Module.Finite R S] in
theorem retainedCompletedGenericPrime_disjoint
    (N : Ideal (R' ⊗[R] S)) [N.IsPrime]
    [N.LiesOver (⊥ : Ideal R')] :
    let T := R' ⊗[R] S
    Disjoint
      (Algebra.algebraMapSubmonoid T (nonZeroDivisors R') : Set T)
      (N : Set T) := by
  let T := R' ⊗[R] S
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

omit [IsDomain R] [IsDomain S] in
/-- A supplied generic prime over zero becomes a maximal ideal after passing
to the generic fibre of the completed finite model. -/
theorem retainedCompletedGenericIdeal_isMaximal
    (N : Ideal (R' ⊗[R] S)) [N.IsPrime]
    [N.LiesOver (⊥ : Ideal R')] :
    (retainedCompletedGenericIdeal
      (R := R) (R' := R') (S := S) (K' := K') N).IsMaximal := by
  let T := R' ⊗[R] S
  let G := retainedCompletedFiniteBaseChangeGenericFiber
    (R := R) (R' := R') (S := S) (K' := K')
  let m := retainedCompletedGenericIdeal
    (R := R) (R' := R') (S := S) (K' := K') N
  let : Algebra T G := Algebra.TensorProduct.rightAlgebra
  let : IsLocalization
      (Algebra.algebraMapSubmonoid T (nonZeroDivisors R')) G :=
    IsLocalization.tensorRight (R := R') (S := T) (A := K')
      (nonZeroDivisors R')
  have hmPrime : m.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid T (nonZeroDivisors R')) G N
      inferInstance
      (retainedCompletedGenericPrime_disjoint
        (R := R) (R' := R') (S := S) N)
  let : m.IsPrime := hmPrime
  let : Module.Finite R' T := Module.Finite.base_change R R' S
  let : Module.Finite K' G := Module.Finite.base_change R' K' T
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := K') m
  rw [Ideal.under_def]
  have hcomapPrime :
      (m.comap (algebraMap K' G)).IsPrime := hmPrime.comap _
  let : (m.comap (algebraMap K' G)).IsPrime := hcomapPrime
  rw [Ideal.eq_bot_of_prime (m.comap (algebraMap K' G))]
  exact Ideal.bot_isMaximal

variable {K : Type uK} {L : Type uL}
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra S L] [IsFractionRing S L]
variable [Algebra R L] [IsScalarTower R S L]
variable [Algebra K L] [IsScalarTower R K L]
variable [Algebra R K'] [IsScalarTower R R' K']
variable [Algebra K K'] [IsScalarTower R K K']

/-- Reassociate the generic fibre of the completed finite model with the
literal field tensor `K' ⊗[K] L`. -/
noncomputable def retainedCompletedGenericFiberEquiv :
    retainedCompletedFiniteBaseChangeGenericFiber
        (R := R) (R' := R') (S := S) (K' := K') ≃ₐ[K']
      (K' ⊗[K] L) := by
  let T := R' ⊗[R] S
  letI : Algebra K' (T ⊗[R'] K') :=
    Algebra.TensorProduct.rightAlgebra
  let eBase : (K' ⊗[R'] T) ≃ₐ[K'] (K' ⊗[R] S) :=
    (Algebra.TensorProduct.commRight R' K' T).trans
      (baseChangeGenericFiberEquiv R R' S K')
  let eGeneric : (K ⊗[R] S) ≃ₐ[K] L :=
    finiteGenericFiberAlgEquiv
      (R := R) (C := S) (K := K) (E := L)
  exact eBase.trans
    (iteratedGenericFiberEquiv R K K' S L eGeneric)

/-- The literal maximal ideal of `K' ⊗[K] L` selected by the supplied
generic prime in the retained completion chain. -/
noncomputable def retainedCompletedGenericTensorIdeal
    (N : Ideal (R' ⊗[R] S)) : Ideal (K' ⊗[K] L) :=
  (retainedCompletedGenericIdeal
      (R := R) (R' := R') (S := S) (K' := K') N).map
    (retainedCompletedGenericFiberEquiv
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K')).toRingEquiv.toRingHom

/-- The retained generic prime therefore selects a literal field component
of the completed generic tensor product. -/
theorem retainedCompletedGenericTensorIdeal_isMaximal
    (N : Ideal (R' ⊗[R] S)) [hNPrime : N.IsPrime]
    [hNOver : N.LiesOver (⊥ : Ideal R')] :
    (retainedCompletedGenericTensorIdeal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N).IsMaximal := by
  let e := retainedCompletedGenericFiberEquiv
    (R := R) (R' := R') (S := S) (K := K) (L := L) (K' := K')
  have hm := retainedCompletedGenericIdeal_isMaximal
    (R := R) (R' := R') (S := S) (K' := K') N
  exact hm.map_bijective
    (f := e.toRingEquiv.toRingHom) e.toRingEquiv.bijective

end LiteralGenericComponent

end EtaleFundamentalGroups

end
