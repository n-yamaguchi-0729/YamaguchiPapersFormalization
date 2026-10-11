/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Maps
import EtaleFundamentalGroups.GenericTensor.FieldComponent.Basic

/-!
# Selected tensor components through an intermediate field

A component of `F' ⊗[K] L` canonically determines a component after first
extending only to an intermediate field `F`.  This file keeps the original
maximal ideal and constructs the second-stage quotient map rather than
postulating a comparison of abstract fields.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uK uF uF' uL

section BaseChange

variable {K : Type uK} {F : Type uF} {F' : Type uF'} {L : Type uL}
variable [Field K] [Field F] [Field F'] [CommRing L]
variable [Algebra K F] [Algebra F F'] [Algebra K F']
variable [IsScalarTower K F F'] [Algebra K L]

/-- The canonical map from the intermediate tensor product to the final
tensor product. -/
noncomputable def genericTensorTowerMap :
    (F ⊗[K] L) →ₐ[K] (F' ⊗[K] L) :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom K F F') (AlgHom.id K L)

/-- The final tensor product as an algebra over the intermediate tensor
product. -/
@[reducible]
noncomputable def genericTensorTowerAlgebra :
    Algebra (F ⊗[K] L) (F' ⊗[K] L) :=
  genericTensorTowerMap.toRingHom.toAlgebra

/-- The canonical base-change equivalence, read over the intermediate
tensor product. -/
noncomputable def genericTensorTowerBaseChangeAlgEquiv :
    let A := F ⊗[K] L
    letI : Algebra A (F' ⊗[K] L) := genericTensorTowerAlgebra
    (A ⊗[F] F') ≃ₐ[A] (F' ⊗[K] L) := by
  let A := F ⊗[K] L
  letI : Algebra A (F' ⊗[K] L) := genericTensorTowerAlgebra
  let eRing : (A ⊗[F] F') ≃+* (F' ⊗[K] L) :=
    (Algebra.TensorProduct.comm F A F').toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange K F F' F' L).toRingEquiv
  exact AlgEquiv.ofRingEquiv (R := A) (f := eRing) fun x => by
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
        change
          Algebra.TensorProduct.cancelBaseChange K F F' F' L
              ((1 : F') ⊗ₜ[F] (x ⊗ₜ[K] y)) =
            genericTensorTowerMap (K := K) (F := F) (F' := F') (L := L)
              (x ⊗ₜ[K] y)
        rw [Algebra.TensorProduct.cancelBaseChange_tmul]
        simp only [genericTensorTowerMap, Algebra.TensorProduct.map_tmul,
          IsScalarTower.toAlgHom_apply, AlgHom.id_apply, Algebra.smul_def, mul_one]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- A finite intermediate field extension makes the canonical tensor tower
finite. -/
theorem genericTensorTower_moduleFinite [FiniteDimensional F F'] :
    letI : Algebra (F ⊗[K] L) (F' ⊗[K] L) := genericTensorTowerAlgebra
    Module.Finite (F ⊗[K] L) (F' ⊗[K] L) := by
  let A := F ⊗[K] L
  let : Algebra A (F' ⊗[K] L) := genericTensorTowerAlgebra
  let : Module.Finite A (A ⊗[F] F') := Module.Finite.base_change F A F'
  exact Module.Finite.equiv
    (genericTensorTowerBaseChangeAlgEquiv (K := K) (F := F) (F' := F') (L := L)).toLinearEquiv

end BaseChange

section FieldComponents

variable {K : Type uK} {F : Type uF} {F' : Type uF'} {L : Type uL}
variable [Field K] [Field F] [Field F'] [Field L]
variable [Algebra K F] [Algebra F F'] [Algebra K F']
variable [IsScalarTower K F F'] [Algebra K L]

/-- The contraction of a selected final tensor component to the intermediate
tensor product. -/
noncomputable def genericTensorTowerIntermediateIdeal
    (m : Ideal (F' ⊗[K] L)) : Ideal (F ⊗[K] L) :=
  m.comap
    (genericTensorTowerMap (K := K) (F := F) (F' := F') (L := L)).toRingHom

/-- A maximal final component contracts to a maximal intermediate component
when the second field extension is finite. -/
theorem genericTensorTowerIntermediateIdeal_isMaximal
    [FiniteDimensional F F'] (m : Ideal (F' ⊗[K] L)) [m.IsMaximal] :
    (genericTensorTowerIntermediateIdeal
      (K := K) (F := F) (F' := F') (L := L) m).IsMaximal := by
  let A := F ⊗[K] L
  let B := F' ⊗[K] L
  let : Algebra A B := genericTensorTowerAlgebra
  let : Module.Finite A B :=
    genericTensorTower_moduleFinite (K := K) (F := F) (F' := F') (L := L)
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap A B)
    (fun x ↦ Algebra.IsIntegral.isIntegral x) m

/-- The canonical embedding of the contracted intermediate component into
the originally selected final component. -/
noncomputable def genericTensorTowerIntermediateComponentMap
    [FiniteDimensional F F'] (m : Ideal (F' ⊗[K] L)) [m.IsMaximal] :
    let n := genericTensorTowerIntermediateIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    GenericTensorFieldComponent n →ₐ[K] GenericTensorFieldComponent m := by
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  letI : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  let g : (F ⊗[K] L) →ₐ[K] GenericTensorFieldComponent m :=
    (Ideal.Quotient.mkₐ K m).comp
      (genericTensorTowerMap (K := K) (F := F) (F' := F') (L := L))
  exact Ideal.Quotient.liftₐ n g fun x hx ↦ by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

@[simp]
theorem genericTensorTowerIntermediateComponentMap_mk
    [FiniteDimensional F F'] (m : Ideal (F' ⊗[K] L)) [m.IsMaximal]
    (x : F ⊗[K] L) :
    genericTensorTowerIntermediateComponentMap
        (K := K) (F := F) (F' := F') (L := L) m
        (Ideal.Quotient.mk
          (genericTensorTowerIntermediateIdeal
            (K := K) (F := F) (F' := F') (L := L) m) x) =
      Ideal.Quotient.mk m
        (genericTensorTowerMap (K := K) (F := F) (F' := F') (L := L) x) := by
  rfl

/-- The intermediate-field algebra structure on the final selected
component, induced through the canonical copy of `F'`. -/
@[reducible]
noncomputable def genericTensorTowerFinalComponentAlgebra
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal] :
    Algebra F (GenericTensorFieldComponent m) :=
  ((genericTensorFieldComponentLeft m).toRingHom.comp
    (algebraMap F F')).toAlgebra

/-- The canonical copy of `F'` in the final component, read as an
`F`-algebra map. -/
noncomputable def genericTensorTowerFinalLeftAlgHom
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal] :
    letI : Algebra F (GenericTensorFieldComponent m) :=
      genericTensorTowerFinalComponentAlgebra
        (K := K) (F := F) (F' := F') (L := L) m
    F' →ₐ[F] GenericTensorFieldComponent m := by
  letI : Algebra F (GenericTensorFieldComponent m) :=
    genericTensorTowerFinalComponentAlgebra
      (K := K) (F := F) (F' := F') (L := L) m
  exact
    { (genericTensorFieldComponentLeft m).toRingHom with
      commutes' := fun _ ↦ rfl }

/-- The contracted component embeds into the final component over the
intermediate field. -/
noncomputable def genericTensorTowerIntermediateComponentAlgHom
    [FiniteDimensional F F'] (m : Ideal (F' ⊗[K] L)) [m.IsMaximal] :
    let n := genericTensorTowerIntermediateIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    letI : Algebra F (GenericTensorFieldComponent m) :=
      genericTensorTowerFinalComponentAlgebra
        (K := K) (F := F) (F' := F') (L := L) m
    GenericTensorFieldComponent n →ₐ[F] GenericTensorFieldComponent m := by
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  letI : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  letI : Algebra F (GenericTensorFieldComponent m) :=
    genericTensorTowerFinalComponentAlgebra
      (K := K) (F := F) (F' := F') (L := L) m
  exact
    { (genericTensorTowerIntermediateComponentMap
        (K := K) (F := F) (F' := F') (L := L) m).toRingHom with
      commutes' := by
        intro x
        change
          Ideal.Quotient.mk m
              (genericTensorTowerMap
                (K := K) (F := F) (F' := F') (L := L)
                ((Algebra.TensorProduct.includeLeft :
                  F →ₐ[K] F ⊗[K] L) x)) =
            genericTensorFieldComponentLeft m (algebraMap F F' x)
        simp [genericTensorTowerMap] }

/-- The second-stage tensor product maps canonically onto the originally
selected final component. -/
noncomputable def genericTensorTowerSecondComponentMap
    [FiniteDimensional F F'] (m : Ideal (F' ⊗[K] L)) [m.IsMaximal] :
    let n := genericTensorTowerIntermediateIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    (F' ⊗[F] GenericTensorFieldComponent n) →ₐ[F']
      GenericTensorFieldComponent m := by
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  letI : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  letI : Algebra F (GenericTensorFieldComponent m) :=
    genericTensorTowerFinalComponentAlgebra
      (K := K) (F := F) (F' := F') (L := L) m
  let gF : (F' ⊗[F] GenericTensorFieldComponent n) →ₐ[F]
      GenericTensorFieldComponent m :=
    Algebra.TensorProduct.productMap
      (genericTensorTowerFinalLeftAlgHom
        (K := K) (F := F) (F' := F') (L := L) m)
      (genericTensorTowerIntermediateComponentAlgHom
        (K := K) (F := F) (F' := F') (L := L) m)
  exact
    { gF.toRingHom with
      commutes' := by
        intro x
        simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe,
          AlgHom.toRingHom_toMonoidHom, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, OneHom.toFun_eq_coe,
          MonoidHom.toOneHom_coe, MonoidHom.coe_ofClass]
        change genericTensorFieldComponentLeft m x *
            genericTensorTowerIntermediateComponentAlgHom
              (K := K) (F := F) (F' := F') (L := L) m
              (1 : GenericTensorFieldComponent n) =
          algebraMap F' (GenericTensorFieldComponent m) x
        rw [map_one, mul_one]
        exact genericTensorFieldComponentLeft_eq_algebraMap m x }

/-- The canonical second-stage map is onto the originally selected
component. -/
theorem genericTensorTowerSecondComponentMap_surjective
    [FiniteDimensional F F'] (m : Ideal (F' ⊗[K] L)) [m.IsMaximal] :
    Function.Surjective
      (genericTensorTowerSecondComponentMap
        (K := K) (F := F) (F' := F') (L := L) m) := by
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  let : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
      refine ⟨a ⊗ₜ[F]
        (Ideal.Quotient.mk n
          ((1 : F) ⊗ₜ[K] b)), ?_⟩
      change genericTensorFieldComponentLeft m a *
          genericTensorTowerIntermediateComponentMap
            (K := K) (F := F) (F' := F') (L := L) m
            (Ideal.Quotient.mk n ((1 : F) ⊗ₜ[K] b)) =
        Ideal.Quotient.mk m (a ⊗ₜ[K] b)
      rw [genericTensorTowerIntermediateComponentMap_mk]
      rw [genericTensorFieldComponentLeft_apply]
      rw [← map_mul]
      congr 1
      simp [genericTensorTowerMap]
  | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      refine ⟨x' + y', ?_⟩
      rw [map_add, hx', hy', map_add]

/-- The maximal ideal selecting the second-stage component corresponding to
the original final component. -/
abbrev genericTensorTowerSecondIdeal
    [FiniteDimensional F F'] (m : Ideal (F' ⊗[K] L)) [m.IsMaximal] :
    let n := genericTensorTowerIntermediateIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    Ideal (F' ⊗[F] GenericTensorFieldComponent n) :=
  RingHom.ker
    (genericTensorTowerSecondComponentMap
      (K := K) (F := F) (F' := F') (L := L) m).toRingHom

/-- The second-stage ideal is maximal because its canonical quotient map is
surjective onto the selected field component. -/
theorem genericTensorTowerSecondIdeal_isMaximal
    [FiniteDimensional F F'] (m : Ideal (F' ⊗[K] L)) [m.IsMaximal] :
    (genericTensorTowerSecondIdeal
      (K := K) (F := F) (F' := F') (L := L) m).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective
    (genericTensorTowerSecondComponentMap
      (K := K) (F := F) (F' := F') (L := L) m)
    (genericTensorTowerSecondComponentMap_surjective
      (K := K) (F := F) (F' := F') (L := L) m)

/-- Factoring a selected tensor component through the intermediate field
does not change the final field component. -/
noncomputable def genericTensorTowerSecondComponentAlgEquiv
    [FiniteDimensional F F'] (m : Ideal (F' ⊗[K] L)) [m.IsMaximal] :
    let n := genericTensorTowerIntermediateIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    let m₂ := genericTensorTowerSecondIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : m₂.IsMaximal :=
      genericTensorTowerSecondIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    GenericTensorFieldComponent m₂ ≃ₐ[F'] GenericTensorFieldComponent m := by
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  letI : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  let m₂ := genericTensorTowerSecondIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  letI : m₂.IsMaximal :=
    genericTensorTowerSecondIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  exact Ideal.quotientKerAlgEquivOfSurjective
    (genericTensorTowerSecondComponentMap_surjective
      (K := K) (F := F) (F' := F') (L := L) m)

end FieldComponents

end EtaleFundamentalGroups

end
