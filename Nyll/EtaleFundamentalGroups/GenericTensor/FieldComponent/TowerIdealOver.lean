/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.Tower

/-!
# A final tensor component above a fixed intermediate component

For a finite field extension `F'/F`, scalar extension makes
`F' ⊗[K] L` a finite faithfully-flat algebra over `F ⊗[K] L`.
Consequently every fixed maximal intermediate component has a maximal final
component above it.  This file packages one canonical choice and records that
the contraction used by `GenericTensorFieldComponentTower` is exactly the
original component.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uK uF uF' uL

section

variable {K : Type uK} {F : Type uF} {F' : Type uF'} {L : Type uL}
variable [Field K] [Field F] [Field F'] [Field L]
variable [Algebra K F] [Algebra F F'] [Algebra K F']
variable [IsScalarTower K F F'] [Algebra K L]
variable [FiniteDimensional F F']

/-- A maximal final tensor component exists above every maximal intermediate
component. -/
theorem exists_genericTensorTowerIdeal_over
    (n : Ideal (F ⊗[K] L)) [n.IsMaximal] :
    ∃ m : Ideal (F' ⊗[K] L),
      m.IsMaximal ∧
        genericTensorTowerIntermediateIdeal
          (K := K) (F := F) (F' := F') (L := L) m = n := by
  let A := F ⊗[K] L
  let B := F' ⊗[K] L
  let : Algebra A B :=
    genericTensorTowerAlgebra
      (K := K) (F := F) (F' := F') (L := L)
  let : Module.Finite A B :=
    genericTensorTower_moduleFinite
      (K := K) (F := F) (F' := F') (L := L)
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let E : (A ⊗[F] F') ≃ₐ[A] B :=
    genericTensorTowerBaseChangeAlgEquiv
      (K := K) (F := F) (F' := F') (L := L)
  let : Module.FaithfullyFlat A (A ⊗[F] F') := inferInstance
  let : Module.FaithfullyFlat A B :=
    Module.FaithfullyFlat.of_linearEquiv
      (R := A) (M := A ⊗[F] F') E.symm.toLinearEquiv
  obtain ⟨m, hm, hover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (R := A) (S := B) n
  refine ⟨m, hm, ?_⟩
  exact hover.over.symm

/-- A canonical maximal final tensor ideal above `n`. -/
noncomputable def genericTensorTowerIdealOver
    (n : Ideal (F ⊗[K] L)) [n.IsMaximal] :
    Ideal (F' ⊗[K] L) :=
  Classical.choose
    (exists_genericTensorTowerIdeal_over
      (K := K) (F := F) (F' := F') (L := L) n)

/-- The chosen final tensor ideal is maximal. -/
theorem genericTensorTowerIdealOver_isMaximal
    (n : Ideal (F ⊗[K] L)) [n.IsMaximal] :
    (genericTensorTowerIdealOver
      (K := K) (F := F) (F' := F') (L := L) n).IsMaximal :=
  (Classical.choose_spec
    (exists_genericTensorTowerIdeal_over
      (K := K) (F := F) (F' := F') (L := L) n)).1

/-- Contracting the chosen final ideal recovers `n` exactly. -/
theorem genericTensorTowerIntermediateIdeal_idealOver
    (n : Ideal (F ⊗[K] L)) [n.IsMaximal] :
    genericTensorTowerIntermediateIdeal
        (K := K) (F := F) (F' := F') (L := L)
        (genericTensorTowerIdealOver
          (K := K) (F := F) (F' := F') (L := L) n) = n :=
  (Classical.choose_spec
    (exists_genericTensorTowerIdeal_over
      (K := K) (F := F) (F' := F') (L := L) n)).2

end

end EtaleFundamentalGroups

end
