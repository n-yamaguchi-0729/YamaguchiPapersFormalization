/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NativeAbsoluteResidueFields
import EtaleFundamentalGroups.Inertia.SeparableClosureAutomorphisms
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Separable residue Galois group objects

Constructs the automorphism-group comparison between a stored algebraic closure and its relative
separable closure. Records preservation of surjectivity and kernels under target group
isomorphisms.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open CategoryTheory

universe u v

/-- Automorphisms of the actual stored field extension. -/
def nativeFieldAutomorphisms (k : Type u) [Field k] (E : Bundled Field.{v})
    (a : Algebra k E) : GrpCat.{v} := by
  letI := a
  exact GrpCat.of (E ≃ₐ[k] E)

/-- The actual relative separable-closure Galois group. -/
def nativeSeparableResidueGroup (k : Type u) [Field k] (E : Bundled Field.{v})
    (a : Algebra k E) : GrpCat.{v} := by
  letI := a
  exact GrpCat.of ((separableClosure k E) ≃ₐ[k] (separableClosure k E))

/-- Restriction on the stored algebraic residue closure is the already
proved actual separable-closure automorphism equivalence. -/
def nativeSeparableResidueIso (k : Type u) [Field k] (E : Bundled Field.{v})
    (a : Algebra k E) (h : letI := a; IsAlgClosure k E) :
    nativeFieldAutomorphisms k E a ≅ nativeSeparableResidueGroup k E a := by
  letI := a
  have : IsAlgClosure k E := h
  exact (separableClosureAutEquiv k E).toGrpIso

/-- The actual relative separable closure with its one stored field structure.
This carrier owner keeps its coefficient algebra and subtype coercion out of
original normalization statements. -/
def nativeSeparableResidueField
    (k : Type u) [Field k] (E : Bundled Field.{v}) (a : Algebra k E.α) :
    Bundled Field.{v} := by
  let := a
  exact ⟨separableClosure k E.α, inferInstance⟩

/-- The actual coefficient inclusion of the stored relative separable closure. -/
def nativeSeparableResidueScalar
    (k : Type u) [Field k] (E : Bundled Field.{v}) (a : Algebra k E.α)
    (z : (nativeSeparableResidueField k E a).α) : E.α :=
  z.val

/-- The stored field automorphism evaluated on a coefficient. -/
def nativeFieldResidueActionScalar
    (k : Type u) [Field k] (E : Bundled Field.{v}) (a : Algebra k E.α)
    (σ : (nativeFieldAutomorphisms k E a).carrier) (z : E.α) : E.α := by
  let := a
  exact (show E.α ≃ₐ[k] E.α from σ).toRingHom.toFun z

/-- The actual separable residue automorphism evaluated in the ambient field.
Only the stored coefficient action is installed, inside this field owner. -/
def nativeSeparableResidueActionScalar
    (k : Type u) [Field k] (E : Bundled Field.{v}) (a : Algebra k E.α)
    (τ : (nativeSeparableResidueGroup k E a).carrier)
    (z : (nativeSeparableResidueField k E a).α) : E.α := by
  let := a
  exact ((show (separableClosure k E.α) ≃ₐ[k] (separableClosure k E.α) from τ
    ).toRingHom.toFun z).val

/-- Restriction through the actual stored isomorphism preserves its ambient
coefficient map. This is the defining `restrictNormal` square. -/
theorem nativeSeparableResidueIso_commutes
    (k : Type u) [Field k] (E : Bundled Field.{v}) (a : Algebra k E.α)
    (h : let := a; IsAlgClosure k E.α)
    (σ : (nativeFieldAutomorphisms k E a).carrier)
    (z : (nativeSeparableResidueField k E a).α) :
    nativeSeparableResidueActionScalar k E a
        ((nativeSeparableResidueIso k E a h).hom.hom'.toFun σ) z =
      nativeFieldResidueActionScalar k E a σ (nativeSeparableResidueScalar k E a z) := by
  let := a
  have : IsAlgClosure k E.α := h
  exact separableClosure_restrictNormal_coefficient k E.α (show E.α ≃ₐ[k] E.α from σ) z

/-- Target transport by a genuine group isomorphism preserves surjectivity. -/
theorem nativeGroupMorphism_comp_iso_surjective
    {D G H : GrpCat.{v}} (f : D ⟶ G) (e : G ≅ H)
    (hf : Function.Surjective f.hom'.toFun) :
    Function.Surjective (f ≫ e.hom).hom'.toFun :=
  (ConcreteCategory.bijective_of_isIso e.hom).surjective.comp hf

/-- Target transport by that same isomorphism preserves the literal kernel. -/
theorem nativeGroupMorphism_comp_iso_ker
    {D G H : GrpCat.{v}} (f : D ⟶ G) (e : G ≅ H) :
    (f ≫ e.hom).hom'.ker = f.hom'.ker :=
  MonoidHom.ker_comp_of_injective f.hom' e.hom.hom'
    (ConcreteCategory.bijective_of_isIso e.hom).injective

end EtaleFundamentalGroups.Inertia

end
