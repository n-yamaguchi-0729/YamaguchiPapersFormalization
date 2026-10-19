/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Module completion and completion at the mapped ideal

For an `R`-algebra `S` and an ideal `I` of `R`, the module completion used by
`AdicCompletion.ofTensorProduct` is built from the quotients
`S / I^n S`.  The ring completion of `S` at the mapped ideal is built from
the same quotients, viewed as quotients by ideals of `S`.  This file constructs
the canonical comparison directly at every finite level and passes it to the
inverse limits.
-/

noncomputable section

namespace EtaleFundamentalGroups

open TensorProduct

universe uR uS

variable {R : Type uR} [CommRing R]
variable {S : Type uS} [CommRing S] [Algebra R S]

private theorem pow_smul_top_eq_restrictScalars_map_pow
    (I : Ideal R) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R S) =
      ((I.map (algebraMap R S)) ^ n : Ideal S).restrictScalars R := by
  rw [← Ideal.map_pow]
  exact Ideal.smul_top_eq_map (I ^ n)

/-- The finite-level linear equivalence between the quotient used in the
module completion and the quotient used in the mapped-ideal ring completion. -/
private noncomputable def mappedIdealQuotientEquiv
    (I : Ideal R) (n : ℕ) :
    (S ⧸ (I ^ n • ⊤ : Submodule R S)) ≃ₗ[R]
      S ⧸ (((I.map (algebraMap R S)) ^ n : Ideal S) • ⊤ : Submodule S S) :=
  (Submodule.quotEquivOfEq _ _
      (pow_smul_top_eq_restrictScalars_map_pow I n)).trans <|
    (Submodule.Quotient.restrictScalarsEquiv R
      ((I.map (algebraMap R S)) ^ n : Ideal S)).trans <|
      (Submodule.quotEquivOfEq _ _
        (by rw [Ideal.smul_eq_mul, Ideal.mul_top])).restrictScalars R

@[simp]
private theorem mappedIdealQuotientEquiv_mk
    (I : Ideal R) (n : ℕ) (x : S) :
    mappedIdealQuotientEquiv I n
        (Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R S)) x) =
      Submodule.Quotient.mk
        (p := (((I.map (algebraMap R S)) ^ n : Ideal S) • ⊤ : Submodule S S)) x := by
  rfl

private theorem mappedIdealQuotientEquiv_transitionMap
    (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (x : S ⧸ (I ^ n • ⊤ : Submodule R S)) :
    AdicCompletion.transitionMap (I.map (algebraMap R S)) S hmn
        (mappedIdealQuotientEquiv I n x) =
      mappedIdealQuotientEquiv I m
        (AdicCompletion.transitionMap I S hmn x) := by
  induction x using Quotient.inductionOn' with
  | _ x => rfl

private theorem mappedIdealQuotientEquiv_symm_transitionMap
    (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (x : S ⧸ (((I.map (algebraMap R S)) ^ n : Ideal S) • ⊤ : Submodule S S)) :
    AdicCompletion.transitionMap I S hmn
        ((mappedIdealQuotientEquiv I n).symm x) =
      (mappedIdealQuotientEquiv I m).symm
        (AdicCompletion.transitionMap (I.map (algebraMap R S)) S hmn x) := by
  apply (mappedIdealQuotientEquiv I m).injective
  rw [LinearEquiv.apply_symm_apply,
    ← mappedIdealQuotientEquiv_transitionMap I hmn,
    LinearEquiv.apply_symm_apply]

/-- The canonical `R`-linear equivalence from the module completion of `S`
along `I` to the ring completion of `S` along the mapped ideal `I S`. -/
noncomputable def mappedIdealCompletionLinearEquiv
    (I : Ideal R) :
    AdicCompletion I S ≃ₗ[R]
      AdicCompletion (I.map (algebraMap R S)) S where
  toFun x :=
    ⟨fun n => mappedIdealQuotientEquiv I n (x.val n), fun {m n} hmn => by
      rw [mappedIdealQuotientEquiv_transitionMap I hmn, x.property hmn]⟩
  invFun x :=
    ⟨fun n => (mappedIdealQuotientEquiv I n).symm (x.val n), fun {m n} hmn => by
      rw [mappedIdealQuotientEquiv_symm_transitionMap I hmn, x.property hmn]⟩
  left_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (mappedIdealQuotientEquiv I n).symm_apply_apply (x.val n)
  right_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (mappedIdealQuotientEquiv I n).apply_symm_apply (x.val n)
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    exact (mappedIdealQuotientEquiv I n).map_add (x.val n) (y.val n)
  map_smul' r x := by
    apply AdicCompletion.ext
    intro n
    exact (mappedIdealQuotientEquiv I n).map_smul r (x.val n)

@[simp]
theorem mappedIdealCompletionLinearEquiv_apply_val
    (I : Ideal R) (x : AdicCompletion I S) (n : ℕ) :
    (mappedIdealCompletionLinearEquiv I x).val n =
      mappedIdealQuotientEquiv I n (x.val n) :=
  rfl

/-- The canonical map from the completed base ring to the completion of `S`
at the mapped ideal. -/
noncomputable def completedBaseToMappedIdealCompletion
    (I : Ideal R) :
    AdicCompletion I R →+*
      AdicCompletion (I.map (algebraMap R S)) S where
  toFun x := mappedIdealCompletionLinearEquiv I
    (AdicCompletion.map I (Algebra.linearMap R S) x)
  map_zero' := by rw [map_zero, map_zero]
  map_add' x y := by rw [map_add, map_add]
  map_one' := by
    apply AdicCompletion.ext
    intro n
    change mappedIdealQuotientEquiv I n
        ((Algebra.linearMap R S).reduceModIdeal (I ^ n)
          ((1 : AdicCompletion I R).val n)) = 1
    rw [AdicCompletion.val_one]
    change mappedIdealQuotientEquiv I n
        ((Algebra.linearMap R S).reduceModIdeal (I ^ n)
          (Submodule.Quotient.mk
            (p := (I ^ n • ⊤ : Submodule R R)) 1)) =
      Submodule.Quotient.mk
        (p := (((I.map (algebraMap R S)) ^ n : Ideal S) • ⊤ : Submodule S S)) 1
    rw [LinearMap.reduceModIdeal_apply, mappedIdealQuotientEquiv_mk]
    exact congrArg Submodule.Quotient.mk (map_one (algebraMap R S))
  map_mul' x y := by
    apply AdicCompletion.ext
    intro n
    change mappedIdealQuotientEquiv I n
        ((Algebra.linearMap R S).reduceModIdeal (I ^ n) ((x * y).val n)) =
      mappedIdealQuotientEquiv I n
          ((Algebra.linearMap R S).reduceModIdeal (I ^ n) (x.val n)) *
        mappedIdealQuotientEquiv I n
          ((Algebra.linearMap R S).reduceModIdeal (I ^ n) (y.val n))
    rw [AdicCompletion.val_mul]
    induction x.val n, y.val n using Quotient.inductionOn₂' with
    | _ x y =>
      change mappedIdealQuotientEquiv I n
          ((Algebra.linearMap R S).reduceModIdeal (I ^ n)
            (Submodule.Quotient.mk
              (p := (I ^ n • ⊤ : Submodule R R)) (x * y))) =
        mappedIdealQuotientEquiv I n
            ((Algebra.linearMap R S).reduceModIdeal (I ^ n)
              (Submodule.Quotient.mk
                (p := (I ^ n • ⊤ : Submodule R R)) x)) *
          mappedIdealQuotientEquiv I n
            ((Algebra.linearMap R S).reduceModIdeal (I ^ n)
              (Submodule.Quotient.mk
                (p := (I ^ n • ⊤ : Submodule R R)) y))
      rw [LinearMap.reduceModIdeal_apply, LinearMap.reduceModIdeal_apply,
        LinearMap.reduceModIdeal_apply, mappedIdealQuotientEquiv_mk,
        mappedIdealQuotientEquiv_mk, mappedIdealQuotientEquiv_mk]
      change Ideal.Quotient.mk _ (algebraMap R S (x * y)) =
        Ideal.Quotient.mk _ (algebraMap R S x) * Ideal.Quotient.mk _ (algebraMap R S y)
      rw [map_mul, map_mul]

@[simp]
theorem completedBaseToMappedIdealCompletion_apply_val
    (I : Ideal R) (x : AdicCompletion I R) (n : ℕ) :
    (completedBaseToMappedIdealCompletion (S := S) I x).val n =
      mappedIdealQuotientEquiv I n
        ((Algebra.linearMap R S).reduceModIdeal (I ^ n) (x.val n)) :=
  rfl

@[simp]
theorem completedBaseToMappedIdealCompletion_algebraMap
    (I : Ideal R) (r : R) :
    completedBaseToMappedIdealCompletion (S := S) I
        (algebraMap R (AdicCompletion I R) r) =
      algebraMap R (AdicCompletion (I.map (algebraMap R S)) S) r := by
  apply AdicCompletion.ext
  intro n
  change mappedIdealQuotientEquiv I n
      ((Algebra.linearMap R S).reduceModIdeal (I ^ n)
        ((algebraMap R (AdicCompletion I R) r).val n)) =
    (algebraMap R (AdicCompletion (I.map (algebraMap R S)) S) r).val n
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply]
  change mappedIdealQuotientEquiv I n
      ((Algebra.linearMap R S).reduceModIdeal (I ^ n)
        (Submodule.Quotient.mk
          (p := (I ^ n • ⊤ : Submodule R R)) r)) =
    Submodule.Quotient.mk
      (p := (((I.map (algebraMap R S)) ^ n : Ideal S) • ⊤ : Submodule S S))
      (algebraMap R S r)
  rw [LinearMap.reduceModIdeal_apply, mappedIdealQuotientEquiv_mk]
  rfl

/-- The canonical algebra structure of the mapped-ideal completion over the
completed base ring. -/
@[reducible]
noncomputable def mappedIdealCompletionAlgebraOverCompletedBase
    (I : Ideal R) :
    Algebra (AdicCompletion I R)
      (AdicCompletion (I.map (algebraMap R S)) S) :=
  (completedBaseToMappedIdealCompletion (S := S) I).toAlgebra

/- Fixing the ideal first makes the source and target of the comparison
algebra concrete before theorem elaboration begins. -/
section CompletedBaseComparison

variable (I : Ideal R)

local instance completedBaseComparisonAlgebra :
    Algebra (AdicCompletion I R)
      (AdicCompletion (I.map (algebraMap R S)) S) :=
  mappedIdealCompletionAlgebraOverCompletedBase I

/-- The canonical completed-base algebra structure restricts to the native
`R`-algebra structure on the mapped-ideal completion. -/
theorem mappedIdealCompletionIsScalarTower
    :
    IsScalarTower R (AdicCompletion I R)
      (AdicCompletion (I.map (algebraMap R S)) S) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (completedBaseToMappedIdealCompletion_algebraMap (S := S) I r).symm

local instance completedBaseComparisonIsScalarTower :
    IsScalarTower R (AdicCompletion I R)
      (AdicCompletion (I.map (algebraMap R S)) S) :=
  mappedIdealCompletionIsScalarTower I

/-- The finite-level comparison intertwines the existing completed-base
scalar action on the module completion with multiplication by the canonical
completed-base map on the mapped-ideal completion. -/
theorem mappedIdealCompletionLinearEquiv_smul
    (r : AdicCompletion I R) (x : AdicCompletion I S) :
    mappedIdealCompletionLinearEquiv I (r • x) =
      r • mappedIdealCompletionLinearEquiv I x := by
  rw [Algebra.smul_def]
  apply AdicCompletion.ext
  intro n
  change mappedIdealQuotientEquiv I n (r.val n • x.val n) =
    mappedIdealQuotientEquiv I n
        ((Algebra.linearMap R S).reduceModIdeal (I ^ n) (r.val n)) *
      mappedIdealQuotientEquiv I n (x.val n)
  induction r.val n, x.val n using Quotient.inductionOn₂' with
  | _ r x =>
    change mappedIdealQuotientEquiv I n
        (Submodule.Quotient.mk
          (p := (I ^ n • ⊤ : Submodule R S)) (r • x)) =
      mappedIdealQuotientEquiv I n
          ((Algebra.linearMap R S).reduceModIdeal (I ^ n)
            (Submodule.Quotient.mk
              (p := (I ^ n • ⊤ : Submodule R R)) r)) *
        mappedIdealQuotientEquiv I n
          (Submodule.Quotient.mk
            (p := (I ^ n • ⊤ : Submodule R S)) x)
    rw [LinearMap.reduceModIdeal_apply, mappedIdealQuotientEquiv_mk,
      mappedIdealQuotientEquiv_mk, mappedIdealQuotientEquiv_mk]
    simp [Algebra.smul_def]

/-- The canonical comparison as a linear equivalence over the completed base
ring. -/
noncomputable def mappedIdealCompletionLinearEquivOverCompletedBase
    :
    AdicCompletion I S ≃ₗ[AdicCompletion I R]
      AdicCompletion (I.map (algebraMap R S)) S := by
  let e : AdicCompletion I S ≃
      AdicCompletion (I.map (algebraMap R S)) S :=
    (mappedIdealCompletionLinearEquiv I).toEquiv
  exact
    { toEquiv := e
      map_add' := fun x y ↦ by
        apply AdicCompletion.ext
        intro n
        exact (mappedIdealQuotientEquiv I n).map_add (x.val n) (y.val n)
      map_smul' := mappedIdealCompletionLinearEquiv_smul I }

@[simp]
theorem mappedIdealCompletionLinearEquiv_of
    (s : S) :
    mappedIdealCompletionLinearEquiv I (AdicCompletion.of I S s) =
      algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) s := by
  apply AdicCompletion.ext
  intro n
  rfl

/-- The canonical algebra homomorphism from the base-changed algebra to the
mapped-ideal completion. -/
noncomputable def tensorProductToMappedIdealCompletionAlgHom
    :
    (AdicCompletion I R ⊗[R] S) →ₐ[AdicCompletion I R]
      AdicCompletion (I.map (algebraMap R S)) S := by
  exact (IsScalarTower.toAlgHom R S
    (AdicCompletion (I.map (algebraMap R S)) S)).liftEquiv
      R (AdicCompletion I R) S
        (AdicCompletion (I.map (algebraMap R S)) S)

@[simp]
theorem tensorProductToMappedIdealCompletionAlgHom_tmul
    (r : AdicCompletion I R) (s : S) :
    tensorProductToMappedIdealCompletionAlgHom I (r ⊗ₜ[R] s) =
      r • algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) s := by
  simp [tensorProductToMappedIdealCompletionAlgHom]

theorem tensorProductToMappedIdealCompletionAlgHom_apply
    (z : (AdicCompletion I R ⊗[R] S)) :
    tensorProductToMappedIdealCompletionAlgHom I z =
      mappedIdealCompletionLinearEquiv I
        (AdicCompletion.ofTensorProduct I S z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r s =>
      simp [mappedIdealCompletionLinearEquiv_smul,
        mappedIdealCompletionLinearEquiv_of]
  | add x y hx hy => simp [hx, hy]

end CompletedBaseComparison

@[reducible]
private noncomputable def mappedIdealCompletionMul
    (I : Ideal R) : Mul (AdicCompletion I S) :=
  ⟨fun x y ↦ (mappedIdealCompletionLinearEquiv I).symm
    (mappedIdealCompletionLinearEquiv I x * mappedIdealCompletionLinearEquiv I y)⟩

@[reducible]
private noncomputable def mappedIdealCompletionOne
    (I : Ideal R) : One (AdicCompletion I S) :=
  ⟨(mappedIdealCompletionLinearEquiv I).symm 1⟩

section MappedIdealCompletionRingConstruction

private theorem mappedIdealCompletionLinearEquiv_mul
    (I : Ideal R)
    (x y : AdicCompletion I S) :
    letI : Mul (AdicCompletion I S) := mappedIdealCompletionMul I
    mappedIdealCompletionLinearEquiv I (x * y) =
      mappedIdealCompletionLinearEquiv I x * mappedIdealCompletionLinearEquiv I y := by
  exact (mappedIdealCompletionLinearEquiv I).apply_symm_apply _

private theorem mappedIdealCompletionLinearEquiv_one
    (I : Ideal R) :
    letI : One (AdicCompletion I S) := mappedIdealCompletionOne I
    mappedIdealCompletionLinearEquiv I (1 : AdicCompletion I S) = 1 := by
  exact (mappedIdealCompletionLinearEquiv I).apply_symm_apply _

/-- The commutative-ring structure on the module completion obtained by using
the canonical finite-level quotient rings.  Its additive structure is the
existing additive structure of the module completion. -/
@[reducible]
noncomputable def mappedIdealCompletionCommRing
    (I : Ideal R) : CommRing (AdicCompletion I S) := by
  letI : Mul (AdicCompletion I S) := mappedIdealCompletionMul I
  letI : One (AdicCompletion I S) := mappedIdealCompletionOne I
  apply CommRing.ofMinimalAxioms
  · exact add_assoc
  · exact zero_add
  · exact neg_add_cancel
  · intro x y z
    apply (mappedIdealCompletionLinearEquiv I).injective
    simp only [mappedIdealCompletionLinearEquiv_mul, mul_assoc]
  · intro x y
    apply (mappedIdealCompletionLinearEquiv I).injective
    simp only [mappedIdealCompletionLinearEquiv_mul, mul_comm]
  · intro x
    apply (mappedIdealCompletionLinearEquiv I).injective
    simp only [mappedIdealCompletionLinearEquiv_mul,
      mappedIdealCompletionLinearEquiv_one, one_mul]
  · intro x y z
    apply (mappedIdealCompletionLinearEquiv I).injective
    simp only [mappedIdealCompletionLinearEquiv_mul, LinearEquiv.map_add,
      mul_add]

end MappedIdealCompletionRingConstruction

section MappedIdealCompletionTransportedRing

/-- The canonical ring equivalence from the module completion along `I` to
the ring completion along the mapped ideal `I S`. -/
noncomputable def mappedIdealCompletionRingEquiv
    (I : Ideal R) :
    letI : CommRing (AdicCompletion I S) := mappedIdealCompletionCommRing I
    AdicCompletion I S ≃+* AdicCompletion (I.map (algebraMap R S)) S := by
  let e : AdicCompletion I S ≃
      AdicCompletion (I.map (algebraMap R S)) S :=
    (mappedIdealCompletionLinearEquiv I).toEquiv
  letI : CommRing (AdicCompletion I S) := mappedIdealCompletionCommRing I
  exact
    { toEquiv := e
      map_add' := fun x y ↦ by
        apply AdicCompletion.ext
        intro n
        exact (mappedIdealQuotientEquiv I n).map_add (x.val n) (y.val n)
      map_mul' := mappedIdealCompletionLinearEquiv_mul I }

@[simp]
theorem mappedIdealCompletionRingEquiv_apply_val
    (I : Ideal R) (x : AdicCompletion I S) (n : ℕ) :
    letI : CommRing (AdicCompletion I S) := mappedIdealCompletionCommRing I
    (mappedIdealCompletionRingEquiv I x).val n =
      mappedIdealQuotientEquiv I n (x.val n) := by
  rfl

/-- The `R`-algebra structure on the module completion obtained from the
canonical comparison with the mapped-ideal ring completion. -/
@[reducible]
noncomputable def mappedIdealCompletionAlgebra
    (I : Ideal R) :
    letI : CommRing (AdicCompletion I S) := mappedIdealCompletionCommRing I
    Algebra R (AdicCompletion I S) := by
  letI : CommRing (AdicCompletion I S) := mappedIdealCompletionCommRing I
  let e : AdicCompletion I S ≃+*
      AdicCompletion (I.map (algebraMap R S)) S :=
    mappedIdealCompletionRingEquiv I
  exact (e.symm.toRingHom.comp
    (algebraMap R (AdicCompletion (I.map (algebraMap R S)) S))).toAlgebra

/-- The canonical `R`-algebra equivalence between the module completion along
`I` and the ring completion along the mapped ideal `I S`. -/
noncomputable def mappedIdealCompletionAlgEquiv
    (I : Ideal R) :
    letI : CommRing (AdicCompletion I S) := mappedIdealCompletionCommRing I
    letI : Algebra R (AdicCompletion I S) := mappedIdealCompletionAlgebra I
    AdicCompletion I S ≃ₐ[R]
      AdicCompletion (I.map (algebraMap R S)) S := by
  letI : CommRing (AdicCompletion I S) := mappedIdealCompletionCommRing I
  let e : AdicCompletion I S ≃+*
      AdicCompletion (I.map (algebraMap R S)) S :=
    mappedIdealCompletionRingEquiv I
  letI : Algebra R (AdicCompletion I S) := mappedIdealCompletionAlgebra I
  exact
    { toRingEquiv := e
      commutes' := fun r ↦ e.apply_symm_apply
        (algebraMap R (AdicCompletion (I.map (algebraMap R S)) S) r) }

@[simp]
theorem mappedIdealCompletionAlgEquiv_apply_val
    (I : Ideal R) (x : AdicCompletion I S) (n : ℕ) :
    letI : CommRing (AdicCompletion I S) := mappedIdealCompletionCommRing I
    letI : Algebra R (AdicCompletion I S) := mappedIdealCompletionAlgebra I
    (mappedIdealCompletionAlgEquiv I x).val n =
      mappedIdealQuotientEquiv I n (x.val n) := by
  rfl

end MappedIdealCompletionTransportedRing

section TensorProductEquivalence

universe u

variable {R₀ S₀ : Type u} [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀]

variable (I : Ideal R₀)

local instance tensorProductMappedIdealCompletionAlgebra :
    Algebra (AdicCompletion I R₀)
      (AdicCompletion (I.map (algebraMap R₀ S₀)) S₀) :=
  mappedIdealCompletionAlgebraOverCompletedBase I

local instance tensorProductMappedIdealCompletionIsScalarTower :
    IsScalarTower R₀ (AdicCompletion I R₀)
      (AdicCompletion (I.map (algebraMap R₀ S₀)) S₀) :=
  mappedIdealCompletionIsScalarTower I

/-- For a finite algebra over a Noetherian ring, the tensor-product model of
completion is canonically linearly equivalent to completion at the mapped
ideal. -/
noncomputable def tensorProductMappedIdealCompletionLinearEquiv
    [IsNoetherianRing R₀] [Module.Finite R₀ S₀] :
    (AdicCompletion I R₀ ⊗[R₀] S₀) ≃ₗ[AdicCompletion I R₀]
      AdicCompletion (I.map (algebraMap R₀ S₀)) S₀ := by
  exact (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I S₀).trans
    (mappedIdealCompletionLinearEquivOverCompletedBase I)

/-- For a finite algebra over a Noetherian ring, base change to the completed
base is canonically the completion at the mapped ideal. -/
noncomputable def tensorProductMappedIdealCompletionAlgEquiv
    [IsNoetherianRing R₀] [Module.Finite R₀ S₀] :
    (AdicCompletion I R₀ ⊗[R₀] S₀) ≃ₐ[AdicCompletion I R₀]
      AdicCompletion (I.map (algebraMap R₀ S₀)) S₀ := by
  let f : (AdicCompletion I R₀ ⊗[R₀] S₀) →ₐ[AdicCompletion I R₀]
      AdicCompletion (I.map (algebraMap R₀ S₀)) S₀ :=
    tensorProductToMappedIdealCompletionAlgHom I
  let e : (AdicCompletion I R₀ ⊗[R₀] S₀) ≃ₗ[AdicCompletion I R₀]
      AdicCompletion (I.map (algebraMap R₀ S₀)) S₀ :=
    tensorProductMappedIdealCompletionLinearEquiv I
  apply AlgEquiv.ofBijective f
  rw [show (⇑f : (AdicCompletion I R₀ ⊗[R₀] S₀) →
      AdicCompletion (I.map (algebraMap R₀ S₀)) S₀) = ⇑e by
    funext z
    exact tensorProductToMappedIdealCompletionAlgHom_apply I z]
  exact e.bijective

/-- The ring-equivalence form of
`tensorProductMappedIdealCompletionAlgEquiv`. -/
noncomputable def tensorProductMappedIdealCompletionRingEquiv
    [IsNoetherianRing R₀] [Module.Finite R₀ S₀] :
    (AdicCompletion I R₀ ⊗[R₀] S₀) ≃+*
      AdicCompletion (I.map (algebraMap R₀ S₀)) S₀ := by
  exact (tensorProductMappedIdealCompletionAlgEquiv I).toRingEquiv

@[simp]
theorem tensorProductMappedIdealCompletionAlgEquiv_apply
    [IsNoetherianRing R₀] [Module.Finite R₀ S₀]
    (z : AdicCompletion I R₀ ⊗[R₀] S₀) :
    tensorProductMappedIdealCompletionAlgEquiv I z =
      tensorProductToMappedIdealCompletionAlgHom I z := by
  simp [tensorProductMappedIdealCompletionAlgEquiv]

end TensorProductEquivalence

section TensorProductFreeEquivalence

variable {R₀ : Type uR} {S₀ : Type uS}
variable [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀]

variable (I : Ideal R₀)

local instance tensorProductMappedIdealCompletionFreeAlgebra :
    Algebra (AdicCompletion I R₀)
      (AdicCompletion (I.map (algebraMap R₀ S₀)) S₀) :=
  mappedIdealCompletionAlgebraOverCompletedBase I

local instance tensorProductMappedIdealCompletionFreeIsScalarTower :
    IsScalarTower R₀ (AdicCompletion I R₀)
      (AdicCompletion (I.map (algebraMap R₀ S₀)) S₀) :=
  mappedIdealCompletionIsScalarTower I

private noncomputable def ofTensorProductEquivOfFiniteFree
    [Module.Free R₀ S₀] [Module.Finite R₀ S₀] :
    (AdicCompletion I R₀ ⊗[R₀] S₀) ≃ₗ[AdicCompletion I R₀]
      AdicCompletion I S₀ := by
  let ι := Module.Free.ChooseBasisIndex R₀ S₀
  let b : Module.Basis ι R₀ S₀ := Module.Free.chooseBasis R₀ S₀
  exact ((AlgebraTensorModule.congr
      (LinearEquiv.refl (AdicCompletion I R₀) (AdicCompletion I R₀))
      b.equivFun).trans
    (AdicCompletion.ofTensorProductEquivOfPiFintype I ι)).trans
      (AdicCompletion.congr I b.equivFun).symm

private theorem ofTensorProductEquivOfFiniteFree_apply
    [Module.Free R₀ S₀] [Module.Finite R₀ S₀]
    (z : AdicCompletion I R₀ ⊗[R₀] S₀) :
    ofTensorProductEquivOfFiniteFree I z =
      AdicCompletion.ofTensorProduct I S₀ z := by
  let ι := Module.Free.ChooseBasisIndex R₀ S₀
  let b : Module.Basis ι R₀ S₀ := Module.Free.chooseBasis R₀ S₀
  change (AdicCompletion.congr I b.equivFun).symm
      (AdicCompletion.ofTensorProductEquivOfPiFintype I ι
        (AlgebraTensorModule.congr
          (LinearEquiv.refl (AdicCompletion I R₀) (AdicCompletion I R₀))
          b.equivFun z)) =
    AdicCompletion.ofTensorProduct I S₀ z
  apply (AdicCompletion.congr I b.equivFun).injective
  rw [LinearEquiv.apply_symm_apply]
  change AdicCompletion.ofTensorProduct I (ι → R₀)
      (AlgebraTensorModule.map LinearMap.id b.equivFun z) =
    AdicCompletion.map I b.equivFun
      (AdicCompletion.ofTensorProduct I S₀ z)
  exact congrArg (fun f => f z)
    (AdicCompletion.ofTensorProduct_naturality I b.equivFun.toLinearMap).symm

/-- For a finite free module, the canonical tensor-to-completion map is
bijective without any universe restriction on the module. -/
theorem ofTensorProduct_bijective_of_finite_free
    [Module.Free R₀ S₀] [Module.Finite R₀ S₀] :
    Function.Bijective (AdicCompletion.ofTensorProduct I S₀) := by
  constructor
  · intro x y hxy
    apply (ofTensorProductEquivOfFiniteFree I).injective
    simpa only [ofTensorProductEquivOfFiniteFree_apply] using hxy
  · intro y
    obtain ⟨x, rfl⟩ := (ofTensorProductEquivOfFiniteFree I).surjective y
    exact ⟨x, (ofTensorProductEquivOfFiniteFree_apply I x).symm⟩

/-- For a finite free algebra, the canonical algebra homomorphism from
completed base change to mapped-ideal completion is bijective, even when the
two rings live in different universes. -/
theorem tensorProductToMappedIdealCompletionAlgHom_bijective_of_finite_free
    [Module.Free R₀ S₀] [Module.Finite R₀ S₀] :
    Function.Bijective
      (tensorProductToMappedIdealCompletionAlgHom (S := S₀) I) := by
  rw [show (⇑(tensorProductToMappedIdealCompletionAlgHom (S := S₀) I) :
      (AdicCompletion I R₀ ⊗[R₀] S₀) →
        AdicCompletion (I.map (algebraMap R₀ S₀)) S₀) =
      fun z ↦ mappedIdealCompletionLinearEquiv I
        (AdicCompletion.ofTensorProduct I S₀ z) by
    funext z
    exact tensorProductToMappedIdealCompletionAlgHom_apply I z]
  exact (mappedIdealCompletionLinearEquiv I).bijective.comp
    (ofTensorProduct_bijective_of_finite_free I)

/-- For a finite free algebra, completed base change is canonically the
completion at the mapped ideal, with no equality constraint on the universes
of the two rings. -/
noncomputable def tensorProductMappedIdealCompletionFreeAlgEquiv
    [Module.Free R₀ S₀] [Module.Finite R₀ S₀] :
    (AdicCompletion I R₀ ⊗[R₀] S₀) ≃ₐ[AdicCompletion I R₀]
      AdicCompletion (I.map (algebraMap R₀ S₀)) S₀ := by
  exact AlgEquiv.ofBijective
    (tensorProductToMappedIdealCompletionAlgHom I)
    (tensorProductToMappedIdealCompletionAlgHom_bijective_of_finite_free I)

/-- The cross-universe ring-equivalence form of
`tensorProductMappedIdealCompletionFreeAlgEquiv`. -/
noncomputable def tensorProductMappedIdealCompletionFreeRingEquiv
    [Module.Free R₀ S₀] [Module.Finite R₀ S₀] :
    (AdicCompletion I R₀ ⊗[R₀] S₀) ≃+*
      AdicCompletion (I.map (algebraMap R₀ S₀)) S₀ := by
  exact (tensorProductMappedIdealCompletionFreeAlgEquiv I).toRingEquiv

@[simp]
theorem tensorProductMappedIdealCompletionFreeAlgEquiv_apply
    [Module.Free R₀ S₀] [Module.Finite R₀ S₀]
    (z : AdicCompletion I R₀ ⊗[R₀] S₀) :
    tensorProductMappedIdealCompletionFreeAlgEquiv I z =
      tensorProductToMappedIdealCompletionAlgHom I z := by
  simp [tensorProductMappedIdealCompletionFreeAlgEquiv]

/-- On the right tensor factor, the cross-universe ring equivalence is the
canonical map from the algebra to its mapped-ideal completion. -/
@[simp]
theorem tensorProductMappedIdealCompletionFreeRingEquiv_includeRight_apply
    [Module.Free R₀ S₀] [Module.Finite R₀ S₀]
    (x : S₀) :
    tensorProductMappedIdealCompletionFreeRingEquiv I
        (Algebra.TensorProduct.includeRight x) =
      AdicCompletion.of (I.map (algebraMap R₀ S₀)) S₀ x := by
  change tensorProductMappedIdealCompletionFreeAlgEquiv I
      (Algebra.TensorProduct.includeRight x) = _
  rw [tensorProductMappedIdealCompletionFreeAlgEquiv_apply,
    Algebra.TensorProduct.includeRight_apply,
    tensorProductToMappedIdealCompletionAlgHom_tmul]
  simp [AdicCompletion.algebraMap_apply]

end TensorProductFreeEquivalence

end EtaleFundamentalGroups

end
