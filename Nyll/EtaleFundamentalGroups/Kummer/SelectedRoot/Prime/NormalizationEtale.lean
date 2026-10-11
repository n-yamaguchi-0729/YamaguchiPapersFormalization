/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Completions.DVR.IntegralExtensionEtaleDescent
import Nyll.EtaleFundamentalGroups.GenericTensor.ComponentRestrictBase
import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.Basic
import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.BaseRingEquiv
import Nyll.EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualTensorTower
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.StandardCompletion

/-!
# Etaleness at the selected root prime

This file connects the literal selected-root localization to the complete
higher-radical factor theorem.  The first junction below refines a fixed
post-root tensor component after extending the left field.  It is the exact
surjective map needed to keep both the original global component and a
chosen completed component fixed.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uK₀ uK₁ uF uL

section ComponentRefinement

variable {K₀ : Type uK₀} {K₁ : Type uK₁}
variable {F : Type uF} {L : Type uL}
variable [Field K₀] [Field K₁] [Field F] [Field L]
variable [Algebra K₀ K₁] [Algebra K₁ F] [Algebra K₀ F]
variable [IsScalarTower K₀ K₁ F]
variable [Algebra K₀ L]

/-- The canonical map from the original tensor product to the tensor product
with a fixed intermediate component.  It simultaneously extends the left
field `K₁ → F` and applies the quotient selecting `m` on the right. -/
noncomputable def genericTensorRefineChosenComponentMap
    (m : Ideal (K₁ ⊗[K₀] L)) [m.IsMaximal] :
    (F ⊗[K₀] L) →ₐ[F]
      (F ⊗[K₁] GenericTensorFieldComponent m) := by
  let M := GenericTensorFieldComponent m
  let target := F ⊗[K₁] M
  letI : Algebra F target := Algebra.TensorProduct.leftAlgebra
  let rightToM : L →ₐ[K₀] M :=
    ((Ideal.Quotient.mkₐ K₁ m).restrictScalars K₀).comp
      (Algebra.TensorProduct.includeRight : L →ₐ[K₀] K₁ ⊗[K₀] L)
  let right : L →ₐ[K₀] target :=
    ((Algebra.TensorProduct.includeRight : M →ₐ[K₁] target).restrictScalars K₀).comp
      rightToM
  exact Algebra.TensorProduct.lift
    (Algebra.ofId F target) right
    (fun _ _ ↦ Commute.all _ _)

@[simp]
theorem genericTensorRefineChosenComponentMap_tmul
    (m : Ideal (K₁ ⊗[K₀] L)) [m.IsMaximal]
    (x : F) (y : L) :
    genericTensorRefineChosenComponentMap m (x ⊗ₜ[K₀] y) =
      x ⊗ₜ[K₁]
        (Ideal.Quotient.mk m
          ((1 : K₁) ⊗ₜ[K₀] y)) := by
  simp [genericTensorRefineChosenComponentMap,
    Algebra.TensorProduct.lift_tmul]

/-- The component-refinement map is onto. -/
theorem genericTensorRefineChosenComponentMap_surjective
    (m : Ideal (K₁ ⊗[K₀] L)) [m.IsMaximal] :
    Function.Surjective
      (genericTensorRefineChosenComponentMap
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m) := by
  let M := GenericTensorFieldComponent m
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      obtain ⟨y₀, rfl⟩ := Ideal.Quotient.mk_surjective y
      induction y₀ using TensorProduct.inductionOn with
      | tmul c l =>
          refine ⟨(x * algebraMap K₁ F c) ⊗ₜ[K₀] l, ?_⟩
          rw [genericTensorRefineChosenComponentMap_tmul
            (K₀ := K₀) (K₁ := K₁)]
          rw [mul_comm x]
          rw [← Algebra.smul_def]
          rw [TensorProduct.smul_tmul]
          congr 1
          change c • (Ideal.Quotient.mkₐ K₁ m) ((1 : K₁) ⊗ₜ[K₀] l) =
            (Ideal.Quotient.mkₐ K₁ m) (c ⊗ₜ[K₀] l)
          rw [← map_smul]
          congr 1
          simp [Algebra.smul_def,
            Algebra.TensorProduct.tmul_mul_tmul]
      | add y₁ y₂ hy₁ hy₂ =>
          obtain ⟨z₁, hz₁⟩ := hy₁
          obtain ⟨z₂, hz₂⟩ := hy₂
          refine ⟨z₁ + z₂, ?_⟩
          simp only [map_add, hz₁, hz₂,
            map_add, TensorProduct.tmul_add]
  | add z₁ z₂ hz₁ hz₂ =>
      obtain ⟨w₁, rfl⟩ := hz₁
      obtain ⟨w₂, rfl⟩ := hz₂
      exact ⟨w₁ + w₂, map_add _ _ _⟩

/-- Pulling back a maximal completed component along the refinement map
selects a maximal component of the original completed tensor product. -/
noncomputable def genericTensorRefineChosenComponentIdeal
    (m : Ideal (K₁ ⊗[K₀] L)) [m.IsMaximal]
    (q : Ideal (F ⊗[K₁] GenericTensorFieldComponent m))
    [q.IsMaximal] : Ideal (F ⊗[K₀] L) :=
  RingHom.ker
    ((Ideal.Quotient.mkₐ F q).comp
      (genericTensorRefineChosenComponentMap m)).toRingHom

theorem genericTensorRefineChosenComponentIdeal_isMaximal
    (m : Ideal (K₁ ⊗[K₀] L)) [m.IsMaximal]
    (q : Ideal (F ⊗[K₁] GenericTensorFieldComponent m))
    [q.IsMaximal] :
    (genericTensorRefineChosenComponentIdeal m q).IsMaximal := by
  let g : (F ⊗[K₀] L) →ₐ[F]
      GenericTensorFieldComponent q :=
    (Ideal.Quotient.mkₐ F q).comp
      (genericTensorRefineChosenComponentMap
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m)
  have hg : Function.Surjective g :=
    Ideal.Quotient.mk_surjective.comp
      (genericTensorRefineChosenComponentMap_surjective
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m)
  exact RingHom.ker_isMaximal_of_surjective g hg

/-- Refining the contracted component by the second-stage component selected
by `m` recovers the original ideal `m` literally. -/
theorem genericTensorRefineChosenComponentIdeal_tower_second
    [FiniteDimensional K₁ F]
    (m : Ideal (F ⊗[K₀] L)) [m.IsMaximal] :
    let n := genericTensorTowerIntermediateIdeal
      (K := K₀) (F := K₁) (F' := F) (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K₀) (F := K₁) (F' := F) (L := L) m
    let q := genericTensorTowerSecondIdeal
      (K := K₀) (F := K₁) (F' := F) (L := L) m
    letI : q.IsMaximal :=
      genericTensorTowerSecondIdeal_isMaximal
        (K := K₀) (F := K₁) (F' := F) (L := L) m
    genericTensorRefineChosenComponentIdeal
      (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) n q = m := by
  dsimp only
  let n := genericTensorTowerIntermediateIdeal
    (K := K₀) (F := K₁) (F' := F) (L := L) m
  let : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K₀) (F := K₁) (F' := F) (L := L) m
  let q := genericTensorTowerSecondIdeal
    (K := K₀) (F := K₁) (F' := F) (L := L) m
  let : q.IsMaximal :=
    genericTensorTowerSecondIdeal_isMaximal
      (K := K₀) (F := K₁) (F' := F) (L := L) m
  have hcomp (z : F ⊗[K₀] L) :
      genericTensorTowerSecondComponentMap
          (K := K₀) (F := K₁) (F' := F) (L := L) m
          (genericTensorRefineChosenComponentMap
            (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) n z) =
        Ideal.Quotient.mk m z := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
        rw [genericTensorRefineChosenComponentMap_tmul]
        change genericTensorFieldComponentLeft m x *
            genericTensorTowerIntermediateComponentMap
              (K := K₀) (F := K₁) (F' := F) (L := L) m
              (Ideal.Quotient.mk n ((1 : K₁) ⊗ₜ[K₀] y)) =
          Ideal.Quotient.mk m (x ⊗ₜ[K₀] y)
        rw [genericTensorTowerIntermediateComponentMap_mk]
        rw [genericTensorFieldComponentLeft_apply]
        rw [← map_mul]
        congr 1
        simp [genericTensorTowerMap]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  ext z
  change
    (Ideal.Quotient.mkₐ F q)
        (genericTensorRefineChosenComponentMap
          (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) n z) = 0 ↔
      z ∈ m
  change
    Ideal.Quotient.mk q
        (genericTensorRefineChosenComponentMap
          (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) n z) = 0 ↔
      z ∈ m
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change
    genericTensorTowerSecondComponentMap
        (K := K₀) (F := K₁) (F' := F) (L := L) m
        (genericTensorRefineChosenComponentMap
          (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) n z) = 0 ↔
      z ∈ m
  rw [hcomp]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The pulled-back component is the same literal quotient field as the
chosen completed component. -/
noncomputable def genericTensorRefineChosenComponentAlgEquiv
    (m : Ideal (K₁ ⊗[K₀] L)) [m.IsMaximal]
    (q : Ideal (F ⊗[K₁] GenericTensorFieldComponent m))
    [q.IsMaximal] :
    let n := genericTensorRefineChosenComponentIdeal m q
    letI : n.IsMaximal :=
      genericTensorRefineChosenComponentIdeal_isMaximal m q
    GenericTensorFieldComponent n ≃ₐ[F]
      GenericTensorFieldComponent q := by
  dsimp only
  let g : (F ⊗[K₀] L) →ₐ[F]
      GenericTensorFieldComponent q :=
    (Ideal.Quotient.mkₐ F q).comp
      (genericTensorRefineChosenComponentMap
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m)
  have hg : Function.Surjective g :=
    Ideal.Quotient.mk_surjective.comp
      (genericTensorRefineChosenComponentMap_surjective
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m)
  exact Ideal.quotientKerAlgEquivOfSurjective hg

end ComponentRefinement

end EtaleFundamentalGroups.Kummer

end
