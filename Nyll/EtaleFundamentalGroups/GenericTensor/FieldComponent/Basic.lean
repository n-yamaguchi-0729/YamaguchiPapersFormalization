/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Compositum
import Mathlib.FieldTheory.Galois.Basic

/-!
# Field components of a generic tensor product

Let `K' / K` be any field extension and let `L / K` be finite.  A maximal
ideal of `K' ⊗_K L` selects a field component.  This file constructs the two
canonical embeddings into that component, proves that their images generate
the component, and records finiteness.  If `L / K` is Galois, the selected
component is Galois over `K'`.

The generation statement is what keeps this construction tied to the chosen
maximal ideal: the quotient map itself is the product map of the two canonical
embeddings.  A later integral-localization argument can therefore supply a
specific maximal ideal and retain its chosen-prime compatibility.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u v w

variable {K : Type u} {K' : Type v} {L : Type w}
variable [Field K] [Field K'] [Field L]
variable [Algebra K K'] [Algebra K L]

/-- The field component of `K' ⊗_K L` selected by a maximal ideal. -/
abbrev GenericTensorFieldComponent
    (m : Ideal (K' ⊗[K] L)) :=
  (K' ⊗[K] L) ⧸ m

noncomputable instance genericTensorFieldComponentField
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] :
    Field (GenericTensorFieldComponent m) :=
  Ideal.Quotient.field m

/-- The canonical copy of the left factor in the selected component. -/
noncomputable def genericTensorFieldComponentLeft
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] :
    K' →ₐ[K] GenericTensorFieldComponent m :=
  (Ideal.Quotient.mkₐ K m).comp
    (Algebra.TensorProduct.includeLeft : K' →ₐ[K] K' ⊗[K] L)

/-- The canonical copy of the right factor in the selected component. -/
noncomputable def genericTensorFieldComponentRight
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] :
    L →ₐ[K] GenericTensorFieldComponent m :=
  (Ideal.Quotient.mkₐ K m).comp
    (Algebra.TensorProduct.includeRight : L →ₐ[K] K' ⊗[K] L)

/-- The algebra structure on a selected tensor component induced by the
right tensor factor.  It is kept explicit rather than installed globally,
because the same component already carries its canonical algebra structure
over the left tensor factor. -/
@[reducible]
noncomputable def genericTensorFieldComponentRightAlgebra
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] :
    Algebra L (GenericTensorFieldComponent m) :=
  (genericTensorFieldComponentRight m).toRingHom.toAlgebra

/-- With the explicit right-factor algebra structure, its algebra map is
literally the canonical right tensor-factor embedding. -/
theorem genericTensorFieldComponentRight_eq_algebraMap
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] :
    letI : Algebra L (GenericTensorFieldComponent m) :=
      genericTensorFieldComponentRightAlgebra m
    genericTensorFieldComponentRight m =
      IsScalarTower.toAlgHom K L (GenericTensorFieldComponent m) := by
  rfl

/-- The direct `K`-algebra structure on a selected component agrees with the
one obtained through the canonical copy of the right tensor factor. -/
theorem genericTensorFieldComponent_right_isScalarTower
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] :
    letI : Algebra L (GenericTensorFieldComponent m) :=
      genericTensorFieldComponentRightAlgebra m
    IsScalarTower K L (GenericTensorFieldComponent m) := by
  let : Algebra L (GenericTensorFieldComponent m) :=
    genericTensorFieldComponentRightAlgebra m
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change Ideal.Quotient.mk m
      ((Algebra.TensorProduct.includeLeft : K' →ₐ[K] K' ⊗[K] L)
        (algebraMap K K' x)) =
    Ideal.Quotient.mk m
      ((Algebra.TensorProduct.includeRight : L →ₐ[K] K' ⊗[K] L)
        (algebraMap K L x))
  exact congrArg (Ideal.Quotient.mk m)
    (DFunLike.congr_fun
      Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap x)

@[simp]
theorem genericTensorFieldComponentLeft_apply
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] (x : K') :
    genericTensorFieldComponentLeft m x =
      Ideal.Quotient.mk m
        ((Algebra.TensorProduct.includeLeft : K' →ₐ[K] K' ⊗[K] L) x) :=
  rfl

@[simp]
theorem genericTensorFieldComponentRight_apply
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] (x : L) :
    genericTensorFieldComponentRight m x =
      Ideal.Quotient.mk m
        ((Algebra.TensorProduct.includeRight : L →ₐ[K] K' ⊗[K] L) x) :=
  rfl

@[simp]
theorem genericTensorFieldComponentLeft_eq_algebraMap
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] (x : K') :
    genericTensorFieldComponentLeft m x =
      algebraMap K' (GenericTensorFieldComponent m) x :=
  rfl

/-- The direct `K`-algebra structure on the quotient agrees with the one
obtained through its canonical copy of `K'`. -/
theorem genericTensorFieldComponent_isScalarTower
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] :
    IsScalarTower K K' (GenericTensorFieldComponent m) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rfl

/-- The product map of the two canonical embeddings is literally the
quotient map belonging to the specified maximal ideal. -/
theorem genericTensorFieldComponent_productMap_eq_quotient
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] :
    Algebra.TensorProduct.productMap
        (genericTensorFieldComponentLeft m)
        (genericTensorFieldComponentRight m) =
      Ideal.Quotient.mkₐ K m := by
  apply Algebra.TensorProduct.ext
  · ext x
    simp [genericTensorFieldComponentLeft]
  · ext x
    simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.productMap_apply_tmul,
      genericTensorFieldComponentLeft_apply, Algebra.TensorProduct.includeLeft_apply,
      genericTensorFieldComponentRight_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [← map_mul]
    congr 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Consequently the selected maximal ideal is exactly the kernel of the
canonical product map into its field component. -/
theorem genericTensorFieldComponent_productMap_ker
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] :
    RingHom.ker
        (Algebra.TensorProduct.productMap
          (genericTensorFieldComponentLeft m)
          (genericTensorFieldComponentRight m)).toRingHom = m := by
  rw [genericTensorFieldComponent_productMap_eq_quotient]
  exact Ideal.mk_ker (I := m)

/-- Both field factors embed in every selected tensor component. -/
theorem genericTensorFieldComponentLeft_injective
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] :
    Function.Injective (genericTensorFieldComponentLeft m) :=
  (genericTensorFieldComponentLeft m).injective

/-- Both field factors embed in every selected tensor component. -/
theorem genericTensorFieldComponentRight_injective
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] :
    Function.Injective (genericTensorFieldComponentRight m) :=
  (genericTensorFieldComponentRight m).injective

/-- The images of `K'` and `L` generate the field component selected by `m`.

This is proved directly from surjectivity of the quotient map, so it retains
the identity of the specified maximal ideal rather than replacing the
component by an abstract common overfield. -/
theorem genericTensorFieldComponent_fieldRange_sup_eq_top
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] :
    (genericTensorFieldComponentLeft m).fieldRange ⊔
        (genericTensorFieldComponentRight m).fieldRange = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a b
    have ha : genericTensorFieldComponentLeft m a ∈
        (genericTensorFieldComponentLeft m).fieldRange ⊔
          (genericTensorFieldComponentRight m).fieldRange :=
      (show (genericTensorFieldComponentLeft m).fieldRange ≤
          (genericTensorFieldComponentLeft m).fieldRange ⊔
            (genericTensorFieldComponentRight m).fieldRange from le_sup_left)
        ⟨a, rfl⟩
    have hb : genericTensorFieldComponentRight m b ∈
        (genericTensorFieldComponentLeft m).fieldRange ⊔
          (genericTensorFieldComponentRight m).fieldRange :=
      (show (genericTensorFieldComponentRight m).fieldRange ≤
          (genericTensorFieldComponentLeft m).fieldRange ⊔
            (genericTensorFieldComponentRight m).fieldRange from le_sup_right)
        ⟨b, rfl⟩
    convert
      ((genericTensorFieldComponentLeft m).fieldRange ⊔
        (genericTensorFieldComponentRight m).fieldRange).mul_mem ha hb using 1
    all_goals
      simp [genericTensorFieldComponentLeft,
        genericTensorFieldComponentRight, ← map_mul]
  · intro x y hx hy
    simpa using
      ((genericTensorFieldComponentLeft m).fieldRange ⊔
        (genericTensorFieldComponentRight m).fieldRange).add_mem hx hy

/-- A selected component is finite over the left tensor factor whenever the
right tensor factor is finite over the original base. -/
noncomputable instance genericTensorFieldComponentFiniteDimensional
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal]
    [FiniteDimensional K L] :
    FiniteDimensional K' (GenericTensorFieldComponent m) := by
  let iK : K' →ₐ[K] GenericTensorFieldComponent m :=
    genericTensorFieldComponentLeft m
  let iL : L →ₐ[K] GenericTensorFieldComponent m :=
    genericTensorFieldComponentRight m
  let K₀ : IntermediateField K (GenericTensorFieldComponent m) :=
    iK.fieldRange
  let L₀ : IntermediateField K (GenericTensorFieldComponent m) :=
    iL.fieldRange
  let : Algebra K K₀ := K₀.algebra'
  let : Algebra K L₀ := L₀.algebra'
  let eK : K' ≃ₐ[K] K₀ := AlgEquiv.ofInjectiveField iK
  let eL : L ≃ₐ[K] L₀ := AlgEquiv.ofInjectiveField iL
  let : FiniteDimensional K L₀ := eL.toLinearEquiv.finiteDimensional
  have hsup : L₀ ⊔ K₀ = ⊤ := by
    simpa [K₀, L₀, sup_comm] using
      genericTensorFieldComponent_fieldRange_sup_eq_top m
  let : FiniteDimensional K₀
      (L₀ ⊔ K₀ : IntermediateField K (GenericTensorFieldComponent m)) :=
    DiscreteValuationField.FieldCompositum.finiteDimensional_sup_over_right_of_left
      L₀ K₀
  let eTop :
      (L₀ ⊔ K₀ : IntermediateField K (GenericTensorFieldComponent m)) ≃+*
        GenericTensorFieldComponent m :=
    ((IntermediateField.equivOfEq hsup).trans
      (IntermediateField.topEquiv :
        (⊤ : IntermediateField K (GenericTensorFieldComponent m)) ≃ₐ[K]
          GenericTensorFieldComponent m)).toRingEquiv
  exact Module.Finite.of_equiv_equiv eK.symm.toRingEquiv eTop (by
    apply RingHom.ext
    intro x
    change algebraMap K' (GenericTensorFieldComponent m) (eK.symm x) =
      (x : GenericTensorFieldComponent m)
    exact congrArg Subtype.val (eK.apply_symm_apply x))

/-- Separability also survives passage to an arbitrary selected component.

This is the quotient-component version of the CFT compositum theorem
`DiscreteValuationField.FieldCompositum.isSeparable_sup_over_right_of_left`;
the formally-unramified base-change proof removes any finiteness requirement
on `K' / K`. -/
noncomputable instance genericTensorFieldComponentIsSeparable
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Algebra.IsSeparable K' (GenericTensorFieldComponent m) := by
  have : Algebra.FormallyUnramified K L :=
    Algebra.FormallyUnramified.of_isSeparable K L
  have : Algebra.FormallyUnramified K' (K' ⊗[K] L) := by
    infer_instance
  let q : K' ⊗[K] L →ₐ[K'] GenericTensorFieldComponent m :=
    Ideal.Quotient.mkₐ K' m
  have : Algebra.FormallyUnramified K'
      (GenericTensorFieldComponent m) :=
    Algebra.FormallyUnramified.of_surjective q
      Ideal.Quotient.mk_surjective
  have : Algebra.EssFiniteType K'
      (GenericTensorFieldComponent m) := by
    infer_instance
  exact Algebra.FormallyUnramified.isSeparable K'
    (GenericTensorFieldComponent m)

/-- A field component of the base change of a finite Galois extension is
Galois over the new base field. -/
noncomputable instance genericTensorFieldComponentIsGalois
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal]
    [FiniteDimensional K L] [IsGalois K L] :
    IsGalois K' (GenericTensorFieldComponent m) := by
  let iK : K' →ₐ[K] GenericTensorFieldComponent m :=
    genericTensorFieldComponentLeft m
  let iL : L →ₐ[K] GenericTensorFieldComponent m :=
    genericTensorFieldComponentRight m
  let K₀ : IntermediateField K (GenericTensorFieldComponent m) :=
    iK.fieldRange
  let L₀ : IntermediateField K (GenericTensorFieldComponent m) :=
    iL.fieldRange
  let : Algebra K K₀ := K₀.algebra'
  let : Algebra K L₀ := L₀.algebra'
  let eK : K' ≃ₐ[K] K₀ := AlgEquiv.ofInjectiveField iK
  let eL : L ≃ₐ[K] L₀ := AlgEquiv.ofInjectiveField iL
  let : FiniteDimensional K L₀ := eL.toLinearEquiv.finiteDimensional
  let : IsGalois K L₀ := IsGalois.of_algEquiv eL
  have hsup : L₀ ⊔ K₀ = ⊤ := by
    simpa [K₀, L₀, sup_comm] using
      genericTensorFieldComponent_fieldRange_sup_eq_top m
  let : IsGalois K₀ (GenericTensorFieldComponent m) :=
    IsGalois.sup_right L₀ K₀ hsup
  exact IsGalois.of_equiv_equiv
    (F := K₀) (E := GenericTensorFieldComponent m)
    (M := K') (N := GenericTensorFieldComponent m)
    (f := eK.symm.toRingEquiv)
    (g := RingEquiv.refl (GenericTensorFieldComponent m)) (by
      apply RingHom.ext
      intro x
      change algebraMap K' (GenericTensorFieldComponent m) (eK.symm x) = (x :
        GenericTensorFieldComponent m)
      exact congrArg Subtype.val (eK.apply_symm_apply x))

/-- A selected component is finite over the right tensor factor whenever
the left tensor factor is finite over the original base.  This is the
right-hand counterpart of `genericTensorFieldComponentFiniteDimensional`;
it is stated as an explicit producer to avoid installing a second global
algebra structure on the quotient component. -/
theorem genericTensorFieldComponentFiniteDimensionalOverRight
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal]
    [FiniteDimensional K K'] :
    letI : Algebra L (GenericTensorFieldComponent m) :=
      genericTensorFieldComponentRightAlgebra m
    FiniteDimensional L (GenericTensorFieldComponent m) := by
  let : Algebra L (GenericTensorFieldComponent m) :=
    genericTensorFieldComponentRightAlgebra m
  let T := K' ⊗[K] L
  let : Algebra L T := Algebra.TensorProduct.rightAlgebra
  let e : (L ⊗[K] K') ≃ₐ[L] T :=
    Algebra.TensorProduct.commRight K L K'
  let : Module.Finite L (L ⊗[K] K') :=
    Module.Finite.base_change K L K'
  let : Module.Finite L T := Module.Finite.equiv e.toLinearEquiv
  let q : T →ₐ[L] GenericTensorFieldComponent m :=
    Ideal.Quotient.mkₐ L m
  exact Module.Finite.of_surjective q.toLinearMap
    Ideal.Quotient.mk_surjective

/-- A canonical maximal ideal, used when no previously chosen integral prime
specifies a component. -/
noncomputable def genericTensorMaximalIdeal : Ideal (K' ⊗[K] L) :=
  Classical.choose (Ideal.exists_maximal (K' ⊗[K] L))

instance genericTensorMaximalIdeal_isMaximal :
    (genericTensorMaximalIdeal (K := K) (K' := K') (L := L)).IsMaximal :=
  Classical.choose_spec (Ideal.exists_maximal (K' ⊗[K] L))

end EtaleFundamentalGroups
