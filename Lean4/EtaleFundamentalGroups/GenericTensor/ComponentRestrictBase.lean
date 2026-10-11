/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GenericTensor.FieldComponent.Basic

/-!
# Restricting the base of a selected generic tensor component

For field towers `K₀ → K₁ → F` and `K₀ → K₁ → L`, the
canonical balancing map

`F ⊗[K₀] L → F ⊗[K₁] L`

is onto.  Consequently a fixed literal maximal component on the right is
the same quotient field as the component cut out by the kernel of the
composite quotient map on the left.  This keeps completed chosen components
fixed while passing to the earlier field used for a common degree bound.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uK₀ uK₁ uF uL

variable {K₀ : Type uK₀} {K₁ : Type uK₁}
variable {F : Type uF} {L : Type uL}
variable [Field K₀] [Field K₁] [Field F] [Field L]
variable [Algebra K₀ K₁] [Algebra K₁ F] [Algebra K₀ F]
variable [IsScalarTower K₀ K₁ F]
variable [Algebra K₀ L] [Algebra K₁ L]
variable [IsScalarTower K₀ K₁ L]

/-- The canonical surjection imposing the additional `K₁`-balancing
relations on a tensor product originally formed over `K₀`. -/
noncomputable def genericTensorRestrictBaseMap :
    (F ⊗[K₀] L) →ₐ[F] (F ⊗[K₁] L) := by
  letI : Algebra F (F ⊗[K₁] L) := Algebra.TensorProduct.leftAlgebra
  exact Algebra.TensorProduct.lift
    (Algebra.ofId F (F ⊗[K₁] L))
    ((Algebra.TensorProduct.includeRight :
      L →ₐ[K₁] F ⊗[K₁] L).restrictScalars K₀)
    (fun _ _ ↦ Commute.all _ _)

@[simp]
theorem genericTensorRestrictBaseMap_tmul (x : F) (y : L) :
    genericTensorRestrictBaseMap (K₀ := K₀) (K₁ := K₁)
        (x ⊗ₜ[K₀] y) =
      x ⊗ₜ[K₁] y := by
  simp [genericTensorRestrictBaseMap,
    Algebra.TensorProduct.lift_tmul]

/-- The base-restriction tensor map is surjective. -/
theorem genericTensorRestrictBaseMap_surjective :
    Function.Surjective
      (genericTensorRestrictBaseMap
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L)) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact ⟨x ⊗ₜ[K₀] y, genericTensorRestrictBaseMap_tmul x y⟩
  | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩

/-- The maximal ideal on the earlier-base tensor product selecting a fixed
maximal component after imposing the `K₁`-balancing relations. -/
noncomputable def genericTensorRestrictBaseIdeal
    (m : Ideal (F ⊗[K₁] L)) [m.IsMaximal] :
    Ideal (F ⊗[K₀] L) :=
  RingHom.ker
    ((Ideal.Quotient.mkₐ F m).comp
      (genericTensorRestrictBaseMap
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L))).toRingHom

/-- The pulled-back component ideal is maximal because its defining map is
onto the same fixed quotient field. -/
theorem genericTensorRestrictBaseIdeal_isMaximal
    (m : Ideal (F ⊗[K₁] L)) [m.IsMaximal] :
    (genericTensorRestrictBaseIdeal
      (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m).IsMaximal := by
  let g : (F ⊗[K₀] L) →ₐ[F] GenericTensorFieldComponent m :=
    (Ideal.Quotient.mkₐ F m).comp
      (genericTensorRestrictBaseMap
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L))
  have hg : Function.Surjective g :=
    Ideal.Quotient.mk_surjective.comp
      (genericTensorRestrictBaseMap_surjective
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L))
  exact RingHom.ker_isMaximal_of_surjective g hg

/-- Restricting the tensor base does not change the selected quotient-field
component. -/
noncomputable def genericTensorRestrictBaseComponentAlgEquiv
    (m : Ideal (F ⊗[K₁] L)) [m.IsMaximal] :
    let n := genericTensorRestrictBaseIdeal
      (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m
    letI : n.IsMaximal := genericTensorRestrictBaseIdeal_isMaximal m
    GenericTensorFieldComponent n ≃ₐ[F] GenericTensorFieldComponent m := by
  dsimp only
  let g : (F ⊗[K₀] L) →ₐ[F] GenericTensorFieldComponent m :=
    (Ideal.Quotient.mkₐ F m).comp
      (genericTensorRestrictBaseMap
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L))
  have hg : Function.Surjective g :=
    Ideal.Quotient.mk_surjective.comp
      (genericTensorRestrictBaseMap_surjective
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L))
  exact Ideal.quotientKerAlgEquivOfSurjective hg

end EtaleFundamentalGroups

end
