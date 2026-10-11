/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TensorProduct.Quotient
import Nyll.SchemeTheory.RingTheory.Ramification.BaseChange.Flat

/-!
# Chosen primes after completion base change

A faithfully flat local base change which maps the old maximal ideal onto
the new maximal ideal carries the maximal ideal of every local algebra to a
maximal ideal of the tensor product.  For maximal-adic completion the two
required closed-fibre facts are provided by the completion API.  Combining
this prime producer with flat-base-change invariance transports the original
ramification index to the completed chosen tensor factor.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe uR uR' uS

/-- In a closed-point-preserving faithfully flat local base change, the
extension of the target maximal ideal to the tensor product is maximal.

Surjectivity onto the quotient is proved directly: modulo the extended
target maximal ideal, every coefficient in `R'` may be replaced by a lift
from `R`, because the residue-field map is surjective and the discrepancy
belongs to the extended source maximal ideal. -/
theorem tensorProduct_map_maximalIdeal_isMaximal_of_residueFieldMap_bijective
    {R : Type uR} {R' : Type uR'} {S : Type uS}
    [CommRing R] [CommRing R'] [CommRing S]
    [IsLocalRing R] [IsLocalRing R'] [IsLocalRing S]
    [Algebra R R'] [Algebra R S]
    [IsLocalHom (algebraMap R R')] [IsLocalHom (algebraMap R S)]
    [Module.FaithfullyFlat R R']
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R'))) :
    let T := R' ⊗[R] S
    letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
    ((IsLocalRing.maximalIdeal S).map (algebraMap S T)).IsMaximal := by
  let T := R' ⊗[R] S
  let : Algebra S T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R S T :=
    Algebra.TensorProduct.right_isScalarTower
  let : Module.FaithfullyFlat S T :=
    Module.FaithfullyFlat.of_linearEquiv
      (R := S) (M := S ⊗[R] R')
      (Algebra.TensorProduct.commRight R S R').symm.toLinearEquiv
  let p := IsLocalRing.maximalIdeal R
  let q := IsLocalRing.maximalIdeal S
  let q' := q.map (algebraMap S T)
  let g : S →+* T ⧸ q' :=
    (Ideal.Quotient.mk q').comp (algebraMap S T)
  have hpq : p.map (algebraMap R S) ≤ q := by
    exact IsLocalRing.map_maximalIdeal_le (algebraMap R S)
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction x using TensorProduct.inductionOn with
    | tmul r' s =>
        obtain ⟨k, hk⟩ := hres.2 (IsLocalRing.residue R' r')
        obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective k
        let d : R' := r' - algebraMap R R' r
        have hdzero : IsLocalRing.residue R' d = 0 := by
          rw [map_sub,
            ← IsLocalRing.ResidueField.map_residue
              (algebraMap R R') r,
            hr, hk, sub_self]
        have hdmax : d ∈ IsLocalRing.maximalIdeal R' :=
          (IsLocalRing.residue_eq_zero_iff d).mp hdzero
        have hdpmap : d ∈ p.map (algebraMap R R') := by
          rw [hmax]
          exact hdmax
        have hdT : algebraMap R' T d ∈ q' := by
          have hdT' : algebraMap R' T d ∈
              (p.map (algebraMap R R')).map (algebraMap R' T) :=
            Ideal.mem_map_of_mem (algebraMap R' T) hdpmap
          have hpT : p.map (algebraMap R T) ≤ q' := by
            calc
              p.map (algebraMap R T) =
                  (p.map (algebraMap R S)).map (algebraMap S T) := by
                rw [Ideal.map_map, IsScalarTower.algebraMap_eq R S T]
              _ ≤ q.map (algebraMap S T) := Ideal.map_mono hpq
              _ = q' := rfl
          apply hpT
          simpa only [Ideal.map_map,
            IsScalarTower.algebraMap_eq R R' T] using hdT'
        have hdiff :
            r' ⊗ₜ[R] s -
                (1 ⊗ₜ[R] (algebraMap R S r * s) : T) ∈ q' := by
          have hmul : algebraMap R' T d * algebraMap S T s ∈ q' :=
            q'.mul_mem_right (algebraMap S T s) hdT
          have hfirst :
              algebraMap R' T r' * algebraMap S T s =
                (r' ⊗ₜ[R] s : T) := by
            rw [Algebra.TensorProduct.algebraMap_apply,
              Algebra.algebraMap_self_apply,
              Algebra.TensorProduct.right_algebraMap_apply,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          have hsecond :
              algebraMap R' T (algebraMap R R' r) *
                  algebraMap S T s =
                (1 ⊗ₜ[R] (algebraMap R S r * s) : T) := by
            rw [← IsScalarTower.algebraMap_apply R R' T,
              IsScalarTower.algebraMap_apply R S T,
              Algebra.TensorProduct.right_algebraMap_apply,
              Algebra.TensorProduct.right_algebraMap_apply,
              Algebra.TensorProduct.tmul_mul_tmul, one_mul]
          simpa only [d, map_sub, sub_mul, hfirst, hsecond] using hmul
        refine ⟨algebraMap R S r * s, ?_⟩
        apply Ideal.Quotient.eq.2
        change algebraMap S T (algebraMap R S r * s) -
          (r' ⊗ₜ[R] s : T) ∈ q'
        rw [Algebra.TensorProduct.right_algebraMap_apply, ← neg_sub]
        exact q'.neg_mem hdiff
    | add x y hx hy =>
        obtain ⟨sx, hsx⟩ := hx
        obtain ⟨sy, hsy⟩ := hy
        refine ⟨sx + sy, ?_⟩
        change g (sx + sy) =
          Ideal.Quotient.mk q' (x + y)
        rw [map_add, map_add, hsx, hsy]
  have hker : RingHom.ker g = q := by
    ext s
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk q' (algebraMap S T s) = 0 ↔ s ∈ q
    rw [Ideal.Quotient.eq_zero_iff_mem]
    simpa [q'] using
      (show s ∈ (q.map (algebraMap S T)).comap
          (algebraMap S T) ↔ s ∈ q by
        rw [Ideal.comap_map_eq_self_of_faithfullyFlat])
  let : q.IsMaximal := IsLocalRing.maximalIdeal.isMaximal S
  let : Field (S ⧸ q) := Ideal.Quotient.field q
  have hfieldKer : IsField (S ⧸ RingHom.ker g) := by
    rw [hker]
    exact Field.toIsField (S ⧸ q)
  have hfieldQuot : IsField (T ⧸ q') :=
    (RingHom.quotientKerEquivOfSurjective hsurj).symm.toMulEquiv.isField
      hfieldKer
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient q').2
    hfieldQuot

/-- The maximal ideal selected in the tensor-product closed fibre is a
prime lying over the new base maximal ideal.  In particular, this supplies
the upper horizontal `LiesOver` instance in the completion square without
choosing an irreducible component. -/
theorem tensorProduct_map_maximalIdeal_liesOver_of_residueFieldMap_bijective
    {R : Type uR} {R' : Type uR'} {S : Type uS}
    [CommRing R] [CommRing R'] [CommRing S]
    [IsLocalRing R] [IsLocalRing R'] [IsLocalRing S]
    [Algebra R R'] [Algebra R S]
    [IsLocalHom (algebraMap R R')] [IsLocalHom (algebraMap R S)]
    [Module.FaithfullyFlat R R']
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R'))) :
    let T := R' ⊗[R] S
    letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
    let q' := (IsLocalRing.maximalIdeal S).map (algebraMap S T)
    q'.IsMaximal ∧ q'.LiesOver (IsLocalRing.maximalIdeal R') := by
  let T := R' ⊗[R] S
  let : Algebra S T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R S T :=
    Algebra.TensorProduct.right_isScalarTower
  let : Algebra R' T := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower R R' T := inferInstance
  let q := IsLocalRing.maximalIdeal S
  let q' := q.map (algebraMap S T)
  have hqmax : q'.IsMaximal :=
    tensorProduct_map_maximalIdeal_isMaximal_of_residueFieldMap_bijective
      hmax hres
  have hunder :
      q'.under R' =
        (q.under R).map (algebraMap R R') :=
    Ideal.under_map_eq_map_under
      (P := q)
      (by
        have hqunder : q.under R = IsLocalRing.maximalIdeal R := by
          simpa [q, Ideal.under_def] using
            IsLocalRing.maximalIdeal_comap (algebraMap R S)
        rw [hqunder, hmax]
        exact IsLocalRing.maximalIdeal.isMaximal R')
      hqmax.ne_top
  refine ⟨hqmax, ?_⟩
  apply Ideal.LiesOver.mk
  rw [hunder]
  have hqunder : q.under R = IsLocalRing.maximalIdeal R := by
    simpa [q, Ideal.under_def] using
      IsLocalRing.maximalIdeal_comap (algebraMap R S)
  rw [hqunder, hmax]

/-- Ramification index is unchanged after a closed-point-preserving
faithfully flat base change, for the canonical maximal ideal in the tensor
product. -/
theorem tensorProduct_map_maximalIdeal_ramificationIdx_eq
    {R : Type uR} {R' : Type uR'} {S : Type uS}
    [CommRing R] [CommRing R'] [CommRing S]
    [IsLocalRing R] [IsLocalRing R'] [IsLocalRing S]
    [Algebra R R'] [Algebra R S]
    [IsLocalHom (algebraMap R R')] [IsLocalHom (algebraMap R S)]
    [Module.FaithfullyFlat R R'] [Module.Flat R S]
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R'))) :
    let T := R' ⊗[R] S
    letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
    ((IsLocalRing.maximalIdeal S).map (algebraMap S T)).ramificationIdx R' =
      (IsLocalRing.maximalIdeal S).ramificationIdx R := by
  let T := R' ⊗[R] S
  let : Algebra S T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R S T :=
    Algebra.TensorProduct.right_isScalarTower
  let : Algebra R' T := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower R R' T := inferInstance
  let : Module.FaithfullyFlat S T :=
    Module.FaithfullyFlat.of_linearEquiv
      (R := S) (M := S ⊗[R] R')
      (Algebra.TensorProduct.commRight R S R').symm.toLinearEquiv
  let p := IsLocalRing.maximalIdeal R
  let q := IsLocalRing.maximalIdeal S
  let p' := IsLocalRing.maximalIdeal R'
  let q' := q.map (algebraMap S T)
  let : q.IsPrime := (IsLocalRing.maximalIdeal.isMaximal S).isPrime
  let : q.LiesOver p :=
    Ideal.LiesOver.mk (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm
  have hgeom :=
    tensorProduct_map_maximalIdeal_liesOver_of_residueFieldMap_bijective
      (R := R) (R' := R') (S := S) hmax hres
  let : q'.IsPrime := hgeom.1.isPrime
  let : q'.LiesOver p' := hgeom.2
  exact ramificationIdx_eq_of_flat_baseChange_mapped_primes
    p q p' q' hmax rfl

/-- After maximal-adic completion of a Noetherian local base DVR, the
canonical maximal ideal in the tensor product has the same ramification
index as the original maximal ideal.

This is the form used after localizing a branch at its height-one generic
point.  The completion map supplies flatness, locality, equality of maximal
ideals, and the residue-field isomorphism. -/
theorem adicCompletion_tensorProduct_maximalIdeal_ramificationIdx_eq
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsNoetherianRing R] [IsLocalRing S]
    [IsDiscreteValuationRing R]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [FaithfulSMul R S] :
    let R' := AdicCompletion (IsLocalRing.maximalIdeal R) R
    let T := R' ⊗[R] S
    letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
    ((IsLocalRing.maximalIdeal S).map (algebraMap S T)).ramificationIdx R' =
      (IsLocalRing.maximalIdeal S).ramificationIdx R := by
  let R' := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let : Module.FaithfullyFlat R R' :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : Module.Flat R S := inferInstance
  exact tensorProduct_map_maximalIdeal_ramificationIdx_eq
    (R' := R') AdicCompletion.maximalIdeal_eq_map.symm
    (AdicCompletion.residueField_map_bijective R)

end EtaleFundamentalGroups

end
