/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Literal tensor-product legs of algebra cocones

The categorical base-change functor stores its objects with the algebra
structure induced by an object of `Under`.  Downstream algebra calculations
use the canonical tensor-product algebra structure instead.  This file is the
single boundary between those two presentations: it exposes literal canonical
algebra homomorphisms, proves that their `Under` morphisms are the mapped
cocone legs, and records naturality and the tensor-symmetry square.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u

/-- The algebra structure carried by an object under `CommRingCat.of R`,
spelled with the underlying type `R`. -/
local instance underCommRingCatAlgebra
    {R : Type u} [CommRing R] (A : Under (CommRingCat.of R)) : Algebra R A :=
  RingHom.toAlgebra A.hom.hom

/-- The literal tensor-product map induced by a leg of a cocone of
`R`-algebras, with the stage algebra in the left tensor coordinate. -/
def filteredTensorToColimitAlgHom
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type u} [SmallCategory J]
    {F : J ⥤ Under (CommRingCat.of R)} (c : Cocone F) (i : J) :
    (F.obj i ⊗[R] A) →ₐ[R] (c.pt ⊗[R] A) :=
  Algebra.TensorProduct.map
    (CommRingCat.toAlgHom (c.ι.app i)) (AlgHom.id R A)

@[simp]
theorem filteredTensorToColimitAlgHom_tmul
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type u} [SmallCategory J]
    {F : J ⥤ Under (CommRingCat.of R)} (c : Cocone F) (i : J)
    (x : F.obj i) (a : A) :
    filteredTensorToColimitAlgHom c i (x ⊗ₜ[R] a) =
      CommRingCat.toAlgHom (c.ι.app i) x ⊗ₜ[R] a := by
  rfl

/-- The same cocone leg in the orientation used by categorical base change:
the fixed algebra is the left tensor coordinate and hence the scalar ring. -/
def filteredBaseChangeCoconeLegAlgHom
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type u} [SmallCategory J]
    {F : J ⥤ Under (CommRingCat.of R)} (c : Cocone F) (i : J) :
    (A ⊗[R] F.obj i) →ₐ[A] (A ⊗[R] c.pt) :=
  Algebra.TensorProduct.map
    (AlgHom.id A A) (CommRingCat.toAlgHom (c.ι.app i))

@[simp]
theorem filteredBaseChangeCoconeLegAlgHom_tmul
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type u} [SmallCategory J]
    {F : J ⥤ Under (CommRingCat.of R)} (c : Cocone F) (i : J)
    (a : A) (x : F.obj i) :
    filteredBaseChangeCoconeLegAlgHom c i (a ⊗ₜ[R] x) =
      a ⊗ₜ[R] CommRingCat.toAlgHom (c.ι.app i) x := by
  rfl

/-- The literal base-change leg is exactly the leg of the categorically
mapped cocone after forgetting back to `Under`. -/
theorem filteredBaseChangeCoconeLegAlgHom_toUnder
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type u} [SmallCategory J]
    {F : J ⥤ Under (CommRingCat.of R)} (c : Cocone F) (i : J) :
    (filteredBaseChangeCoconeLegAlgHom c i).toUnder =
      ((CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of A)).mapCocone c).ι.app i :=
  rfl

/-- Naturality of the literal base-change cocone legs. -/
theorem filteredBaseChangeCoconeLegAlgHom_naturality
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type u} [SmallCategory J]
    {F : J ⥤ Under (CommRingCat.of R)} (c : Cocone F)
    {i j : J} (f : i ⟶ j) :
    (filteredBaseChangeCoconeLegAlgHom c j).comp
        (Algebra.TensorProduct.map (AlgHom.id A A)
          (CommRingCat.toAlgHom (F.map f))) =
      filteredBaseChangeCoconeLegAlgHom c i := by
  apply Algebra.TensorProduct.ext_ring
  ext x
  have h := congrArg (fun q ↦ q.right x) (c.w f)
  change CommRingCat.toAlgHom (c.ι.app j)
      (CommRingCat.toAlgHom (F.map f) x) =
    CommRingCat.toAlgHom (c.ι.app i) x at h
  exact congrArg (fun y ↦ (1 : A) ⊗ₜ[R] y) h

/-- Swapping tensor factors intertwines the two literal versions of a cocone
leg. -/
theorem filteredBaseChangeCoconeLegAlgHom_comm
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type u} [SmallCategory J]
    {F : J ⥤ Under (CommRingCat.of R)} (c : Cocone F) (i : J)
    (z : F.obj i ⊗[R] A) :
    filteredBaseChangeCoconeLegAlgHom c i
        ((Algebra.TensorProduct.comm R (F.obj i) A) z) =
      (Algebra.TensorProduct.comm R c.pt A)
        (filteredTensorToColimitAlgHom c i z) := by
  exact (Algebra.TensorProduct.comm_comp_map_apply
    (CommRingCat.toAlgHom (c.ι.app i)) (AlgHom.id R A) z).symm

end EtaleFundamentalGroups

end
