/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Completions.Retained.NormalizationPrimeChain
import Nyll.EtaleFundamentalGroups.Normalization.Primes.MinimalLocalizationDomain

/-!
# The retained tensor localization inside its chosen component field

A retained generic prime `N` selects a literal field component `Omega` of
the completed generic tensor product.  If `N` lies below a tensor prime
`Q`, the component map sends every element outside `Q` to a unit and hence
extends canonically to the localization at `Q`.

Once that localization has independently been shown to be a domain, the
extended map is injective: the kernel `N` has already vanished after
localization.  The generic-fibre localization presentation then shows that
`Omega` is the fraction field of the localized tensor ring.  Neither
surjectivity nor bijectivity of the finite-model component map is assumed.
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

/-- The canonical algebra structure on the chosen retained component field
coming from localization of the completed finite model at `Q`. -/
@[reducible]
noncomputable def retainedCompletedChosenComponentLocalizationAlgebra
    (N Q : Ideal (R' ⊗[R] S)) [N.IsPrime]
    [N.LiesOver (⊥ : Ideal R')] [Q.IsPrime] (hNQ : N ≤ Q) :
    Algebra (Localization.AtPrime Q)
      (GenericTensorFieldComponent
        (retainedCompletedGenericTensorIdeal
          (R := R) (R' := R') (S := S) (K := K) (L := L)
          (K' := K') N)) := by
  let m := retainedCompletedGenericTensorIdeal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  letI : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let Ω := GenericTensorFieldComponent m
  let r'ΩAlgebra : Algebra R' Ω :=
    genericTensorFieldComponentLeftScalarAlgebra (R := R') m
  letI : Algebra R' Ω := r'ΩAlgebra
  let j := retainedCompletedChosenComponentAlgHom
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  exact
    (IsLocalization.lift
      (M := Q.primeCompl) (S := Localization.AtPrime Q)
      (g := j.toRingHom) fun y ↦ by
        rw [isUnit_iff_ne_zero]
        intro hy
        apply y.2
        apply hNQ
        rw [← retainedCompletedChosenComponentAlgHom_ker
          (R := R) (R' := R') (S := S) (K := K) (L := L)
          (K' := K') N]
        change j y.1 = 0
        exact hy).toAlgebra

/-- The localization map extends the original retained finite-model map. -/
@[simp]
theorem retainedCompletedChosenComponentLocalizationAlgebra_algebraMap
    (N Q : Ideal (R' ⊗[R] S)) [N.IsPrime]
    [N.LiesOver (⊥ : Ideal R')] [Q.IsPrime] (hNQ : N ≤ Q)
    (x : R' ⊗[R] S) :
    let m := retainedCompletedGenericTensorIdeal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    letI : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    let Ω := GenericTensorFieldComponent m
    letI : Algebra R' Ω :=
      genericTensorFieldComponentLeftScalarAlgebra (R := R') m
    letI := retainedCompletedChosenComponentLocalizationAlgebra
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N Q hNQ
    algebraMap (Localization.AtPrime Q) Ω
        (algebraMap (R' ⊗[R] S) (Localization.AtPrime Q) x) =
      retainedCompletedChosenComponentAlgHom
        (R := R) (R' := R') (S := S) (K := K) (L := L)
        (K' := K') N x := by
  let m := retainedCompletedGenericTensorIdeal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
  let Ω := GenericTensorFieldComponent m
  let r'ΩAlgebra : Algebra R' Ω :=
    genericTensorFieldComponentLeftScalarAlgebra (R := R') m
  let : Algebra R' Ω := r'ΩAlgebra
  let j := retainedCompletedChosenComponentAlgHom
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let := retainedCompletedChosenComponentLocalizationAlgebra
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N Q hNQ
  change IsLocalization.lift _
      (algebraMap (R' ⊗[R] S) (Localization.AtPrime Q) x) = j x
  exact IsLocalization.lift_eq _ x

/-- With the component map used as the direct `T`-algebra structure, the
canonical localization map forms the expected scalar tower. -/
theorem retainedCompletedChosenComponentLocalization_isScalarTower
    (N Q : Ideal (R' ⊗[R] S)) [N.IsPrime]
    [N.LiesOver (⊥ : Ideal R')] [Q.IsPrime] (hNQ : N ≤ Q) :
    let m := retainedCompletedGenericTensorIdeal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    letI : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    let Ω := GenericTensorFieldComponent m
    letI : Algebra R' Ω :=
      genericTensorFieldComponentLeftScalarAlgebra (R := R') m
    let j := retainedCompletedChosenComponentAlgHom
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    letI : Algebra (R' ⊗[R] S) Ω :=
      j.toAlgebra
    letI := retainedCompletedChosenComponentLocalizationAlgebra
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N Q hNQ
    IsScalarTower (R' ⊗[R] S) (Localization.AtPrime Q)
      Ω := by
  dsimp only
  let m := retainedCompletedGenericTensorIdeal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
  let Ω := GenericTensorFieldComponent m
  let r'ΩAlgebra : Algebra R' Ω :=
    genericTensorFieldComponentLeftScalarAlgebra (R := R') m
  let : Algebra R' Ω := r'ΩAlgebra
  let j := retainedCompletedChosenComponentAlgHom
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let : Algebra (R' ⊗[R] S) (GenericTensorFieldComponent m) :=
    j.toAlgebra
  let := retainedCompletedChosenComponentLocalizationAlgebra
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N Q hNQ
  apply IsScalarTower.of_algebraMap_eq'
  rw [RingHom.algebraMap_toAlgebra]
  exact (IsLocalization.lift_comp _).symm

/-- The literal retained generic tensor component is the fraction field of
the localization at any containing prime once that localization has been
shown to be a domain. -/
theorem retainedCompletedChosenComponentLocalization_isFractionRing
    (N Q : Ideal (R' ⊗[R] S)) [N.IsPrime]
    [N.LiesOver (⊥ : Ideal R')] [Q.IsPrime]
    [IsDomain (Localization.AtPrime Q)] (hNQ : N ≤ Q) :
    let m := retainedCompletedGenericTensorIdeal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    letI : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    let Ω := GenericTensorFieldComponent m
    letI : Algebra R' Ω :=
      genericTensorFieldComponentLeftScalarAlgebra (R := R') m
    letI := retainedCompletedChosenComponentLocalizationAlgebra
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N Q hNQ
    IsFractionRing (Localization.AtPrime Q) Ω := by
  let T := R' ⊗[R] S
  let W := Localization.AtPrime Q
  let G₀ := retainedCompletedFiniteBaseChangeGenericFiber
    (R := R) (R' := R') (S := S) (K' := K')
  let e := retainedCompletedGenericFiberEquiv
    (R := R) (R' := R') (S := S) (K := K) (L := L) (K' := K')
  let m := retainedCompletedGenericTensorIdeal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let Ω := GenericTensorFieldComponent m
  let : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
  let r'ΩAlgebra : Algebra R' Ω :=
    genericTensorFieldComponentLeftScalarAlgebra (R := R') m
  let : Algebra R' Ω := r'ΩAlgebra
  let j := retainedCompletedChosenComponentAlgHom
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let : Algebra W Ω :=
    retainedCompletedChosenComponentLocalizationAlgebra
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N Q hNQ
  let : Module.Finite R' T := Module.Finite.base_change R R' S
  let : Algebra.IsIntegral R' T := Algebra.IsIntegral.of_finite R' T
  have hNMapBot : N.map (algebraMap T W) = ⊥ :=
    prime_liesOver_bot_map_eq_bot_localizationAtPrime_of_isDomain
      (R := R') N Q hNQ
  have hjInjective : Function.Injective (algebraMap W Ω) := by
    refine (IsLocalization.lift_injective_iff _).2 ?_
    intro x y
    constructor
    · intro hxy
      have h := congrArg (algebraMap W Ω) hxy
      change IsLocalization.lift _ (algebraMap T W x) =
        IsLocalization.lift _ (algebraMap T W y) at h
      rw [IsLocalization.lift_eq _ x, IsLocalization.lift_eq _ y] at h
      exact h
    · intro hxy
      have hxyN : x - y ∈ N := by
        rw [← retainedCompletedChosenComponentAlgHom_ker
          (R := R) (R' := R') (S := S) (K := K) (L := L)
          (K' := K') N, RingHom.mem_ker, map_sub, sub_eq_zero]
        exact hxy
      have hxyMap :
          algebraMap T W (x - y) ∈ N.map (algebraMap T W) :=
        Ideal.mem_map_of_mem (algebraMap T W) hxyN
      have hxyZero : algebraMap T W (x - y) = 0 := by
        rw [← Ideal.mem_bot, ← hNMapBot]
        exact hxyMap
      simpa only [map_sub, sub_eq_zero] using hxyZero
  let : FaithfulSMul W Ω :=
    (faithfulSMul_iff_algebraMap_injective W Ω).mpr hjInjective
  let : Algebra T G₀ := Algebra.TensorProduct.rightAlgebra
  let M : Submonoid T :=
    Algebra.algebraMapSubmonoid T (nonZeroDivisors R')
  let : IsLocalization M G₀ :=
    IsLocalization.tensorRight (R := R') (S := T) (A := K')
      (nonZeroDivisors R')
  have hdisjoint : Disjoint (M : Set T) (N : Set T) :=
    retainedCompletedGenericPrime_disjoint
      (R := R) (R' := R') (S := S) N
  apply IsFractionRing.of_field
  intro z
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
  let t₀ : G₀ := e.symm t
  obtain ⟨⟨x, s⟩, ht⟩ := IsLocalization.surj M t₀
  have hsN : (s : T) ∉ N := by
    exact hdisjoint.notMem_of_mem_left s.2
  have hjs : j (s : T) ≠ 0 := by
    intro hs
    apply hsN
    rw [← retainedCompletedChosenComponentAlgHom_ker
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N]
    change j (s : T) = 0
    exact hs
  have hsDenominator :
      algebraMap W Ω (algebraMap T W (s : T)) ≠ 0 := by
    change IsLocalization.lift _ (algebraMap T W (s : T)) ≠ 0
    rw [IsLocalization.lift_eq _ (s : T)]
    exact hjs
  refine ⟨algebraMap T W x, algebraMap T W (s : T), ?_⟩
  apply (eq_div_iff hsDenominator).2
  rw [
    retainedCompletedChosenComponentLocalizationAlgebra_algebraMap
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N Q hNQ,
    retainedCompletedChosenComponentLocalizationAlgebra_algebraMap
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N Q hNQ]
  change Ideal.Quotient.mk m t *
      Ideal.Quotient.mk m (e (algebraMap T G₀ (s : T))) =
    Ideal.Quotient.mk m (e (algebraMap T G₀ x))
  have hImage :=
    congrArg (fun u : G₀ ↦ Ideal.Quotient.mk m (e u)) ht
  simpa [t₀] using hImage

end EtaleFundamentalGroups

end
