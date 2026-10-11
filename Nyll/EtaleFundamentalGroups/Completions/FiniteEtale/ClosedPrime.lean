/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Closed primes in a completion base change

The closed prime selected in a finite algebra need not be the unique closed
prime.  Nevertheless, extension along a faithfully flat local base change
with unchanged residue field carries that particular prime to a maximal
ideal of the tensor product.  For maximal-adic completion this gives the
canonical completed closed point before any local factor is split off.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe uR uR' uS

/-- Let `q` be any maximal ideal over the closed point of a local ring `R`.
After a closed-point-preserving faithfully flat local base change `R → R'`
with unchanged residue field, the extension of `q` to `R' ⊗[R] S` is
maximal.

No local-ring structure on `S` and no uniqueness hypothesis on `q` is used.
Modulo the extended ideal, every coefficient of `R'` can be replaced by a
residue lift from `R`, leaving precisely the field `S/q`. -/
theorem tensorProduct_map_isMaximal_of_residueFieldMap_bijective
    {R : Type uR} {R' : Type uR'} {S : Type uS}
    [CommRing R] [CommRing R'] [CommRing S]
    [IsLocalRing R] [IsLocalRing R']
    [Algebra R R'] [Algebra R S]
    [IsLocalHom (algebraMap R R')]
    [Module.FaithfullyFlat R R']
    (q : Ideal S) [q.IsMaximal]
    [q.LiesOver (IsLocalRing.maximalIdeal R)]
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R'))) :
    let T := R' ⊗[R] S
    letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
    (q.map (algebraMap S T)).IsMaximal := by
  let T := R' ⊗[R] S
  let : Algebra S T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R S T :=
    Algebra.TensorProduct.right_isScalarTower
  let : Module.FaithfullyFlat S T :=
    Module.FaithfullyFlat.of_linearEquiv
      (R := S) (M := S ⊗[R] R')
      (Algebra.TensorProduct.commRight R S R').symm.toLinearEquiv
  let p := IsLocalRing.maximalIdeal R
  let q' := q.map (algebraMap S T)
  let g : S →+* T ⧸ q' :=
    (Ideal.Quotient.mk q').comp (algebraMap S T)
  have hpq : p.map (algebraMap R S) ≤ q := by
    rw [Ideal.map_le_iff_le_comap]
    exact (q.over_def p).le
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
        change g (sx + sy) = Ideal.Quotient.mk q' (x + y)
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
  let : Field (S ⧸ q) := Ideal.Quotient.field q
  have hfieldKer : IsField (S ⧸ RingHom.ker g) := by
    rw [hker]
    exact Field.toIsField (S ⧸ q)
  have hfieldQuot : IsField (T ⧸ q') :=
    (RingHom.quotientKerEquivOfSurjective hsurj).symm.toMulEquiv.isField
      hfieldKer
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient q').2
    hfieldQuot

/-- The extended selected closed point lies over the new closed point. -/
theorem tensorProduct_map_liesOver_maximalIdeal_of_residueFieldMap_bijective
    {R : Type uR} {R' : Type uR'} {S : Type uS}
    [CommRing R] [CommRing R'] [CommRing S]
    [IsLocalRing R] [IsLocalRing R']
    [Algebra R R'] [Algebra R S]
    [IsLocalHom (algebraMap R R')]
    [Module.FaithfullyFlat R R']
    (q : Ideal S) [q.IsMaximal]
    [q.LiesOver (IsLocalRing.maximalIdeal R)]
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R R'))) :
    let T := R' ⊗[R] S
    letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
    let q' := q.map (algebraMap S T)
    q'.IsMaximal ∧ q'.LiesOver (IsLocalRing.maximalIdeal R') := by
  let T := R' ⊗[R] S
  let : Algebra S T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R S T :=
    Algebra.TensorProduct.right_isScalarTower
  let : Algebra R' T := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower R R' T := inferInstance
  let q' := q.map (algebraMap S T)
  have hqmax : q'.IsMaximal :=
    tensorProduct_map_isMaximal_of_residueFieldMap_bijective
      (R := R) (R' := R') q hmax hres
  have hunder :
      q'.under R' =
        (q.under R).map (algebraMap R R') :=
    Ideal.under_map_eq_map_under
      (P := q)
      (by
        rw [← q.over_def (IsLocalRing.maximalIdeal R), hmax]
        exact IsLocalRing.maximalIdeal.isMaximal R')
      hqmax.ne_top
  refine ⟨hqmax, ?_⟩
  apply Ideal.LiesOver.mk
  rw [hunder, ← q.over_def (IsLocalRing.maximalIdeal R), hmax]

/-- Specialization to maximal-adic completion.  This transports an
arbitrarily chosen closed prime of `S` to a canonical maximal ideal of the
completion tensor product, with exact map equality built into its
definition. -/
theorem adicCompletion_tensorProduct_map_liesOver_maximalIdeal
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsLocalRing R]
    [Algebra R S]
    (q : Ideal S) [q.IsMaximal]
    [q.LiesOver (IsLocalRing.maximalIdeal R)] :
    let R' := AdicCompletion (IsLocalRing.maximalIdeal R) R
    let T := R' ⊗[R] S
    letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
    let q' := q.map (algebraMap S T)
    q'.IsMaximal ∧ q'.LiesOver (IsLocalRing.maximalIdeal R') := by
  let R' := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let : Module.FaithfullyFlat R R' :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact
    tensorProduct_map_liesOver_maximalIdeal_of_residueFieldMap_bijective
      (R' := R') q AdicCompletion.maximalIdeal_eq_map.symm
      (AdicCompletion.residueField_map_bijective R)

/-- Completion base change of a finite etale algebra, together with the
canonical completed closed point selected by an original maximal ideal. -/
theorem adicCompletion_finiteEtale_closedPrime
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsLocalRing R]
    [Algebra R S] [Module.Finite R S] [Algebra.Etale R S]
    (q : Ideal S) [q.IsMaximal]
    [q.LiesOver (IsLocalRing.maximalIdeal R)] :
    let R' := AdicCompletion (IsLocalRing.maximalIdeal R) R
    let T := R' ⊗[R] S
    letI : Algebra R' T := Algebra.TensorProduct.leftAlgebra
    letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
    let q' := q.map (algebraMap S T)
    q'.IsMaximal ∧ q'.LiesOver (IsLocalRing.maximalIdeal R') ∧
      Module.Finite R' T ∧ Algebra.Etale R' T := by
  let R' := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let T := R' ⊗[R] S
  let : Algebra R' T := Algebra.TensorProduct.leftAlgebra
  let : Algebra S T := Algebra.TensorProduct.rightAlgebra
  have hq := adicCompletion_tensorProduct_map_liesOver_maximalIdeal
    (R := R) (S := S) q
  exact ⟨hq.1, hq.2, inferInstance, inferInstance⟩

end EtaleFundamentalGroups

end
