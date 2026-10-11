/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GenericTensor.FilteredColimit.IdempotentDescent
import Nyll.EtaleFundamentalGroups.Inertia.EquivariantIdempotentDescent
import Nyll.EtaleFundamentalGroups.Inertia.InvariantBaseChange
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkAlgebraColimit
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkAffineGenericDescent
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Filtered.FinallySmall
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.TensorProduct.Maps


/-!
# Finite idempotent decompositions descend to pointed étale neighborhoods

A finite complete orthogonal family in an arbitrary algebra after base
change to the actual geometric stalk descends to one actual pointed étale
neighborhood. An affine refinement retains the same idempotents and their
literal germ images. All scalar structures are the existing structures on
the actual objects under the base ring.

This supplies the finite idempotent descent in external Stacks tag 0BSR,
needed for [Stacks, Tag 0BST](https://stacks.math.columbia.edu/tag/0BST). Prime-fiber finiteness and
residue-extension comparisons are separate prerequisites.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u w

variable {R : CommRingCat.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω)

private theorem neighborhoodGerm_naturality
    {W V : (Spec R).Etale} (j : V ⟶ W)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj V)
    (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W)
    (hj : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.map j v = t) :
    geometricNeighborhoodAlgebraMap R j ≫ geometricNeighborhoodGerm φ V v =
      geometricNeighborhoodGerm φ W t := by
  apply Under.UnderMorphism.ext
  change j.left.appTop ≫ geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) V v =
    geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W t
  have h := (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber_w
    j v (etaleSections (Spec R))
  rw [hj] at h
  exact h

private theorem exists_pointed_completeOrthogonalIdempotents
    {B ι : Type u} [CommRing B] [Algebra R B] [Fintype ι]
    (e : ι → ((geometricStalkSmallAlgebraCocone φ).pt ⊗[R] B))
    (he : CompleteOrthogonalIdempotents e) :
    ∃ (W : (Spec R).Etale)
      (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W)
      (eW : ι → (geometricNeighborhoodAlgebra R W ⊗[R] B)),
      CompleteOrthogonalIdempotents eW ∧
        ∀ a, Algebra.TensorProduct.map
          (CommRingCat.toAlgHom (geometricNeighborhoodGerm φ W t))
          (AlgHom.id R B) (eW a) = e a := by
  obtain ⟨i, eᵢ, heᵢ, hmap⟩ :=
    exists_completeOrthogonalIdempotents_stage_of_filteredColimit
      (geometricStalkSmallAlgebraDiagram φ) (geometricStalkSmallAlgebraCocone φ)
      (geometricStalkSmallAlgebraCoconeIsColimit φ) e he
  let j := (FinallySmall.fromFilteredFinalModel
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.Elementsᵒᵖ).obj i
  exact ⟨j.unop.obj, j.unop.val, eᵢ, heᵢ, hmap⟩

/-- Every finite complete orthogonal family in the actual geometric-stalk
base change of an arbitrary algebra descends to an actual affine pointed
étale neighborhood, with its prescribed literal germ images. -/
theorem geometricStalk_exists_affine_completeOrthogonalIdempotents
    {B ι : Type u} [CommRing B] [Algebra R B] [Fintype ι]
    (e : ι → ((geometricStalkSmallAlgebraCocone φ).pt ⊗[R] B))
    (he : CompleteOrthogonalIdempotents e) :
    ∃ (V : (Spec R).Etale)
      (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj V),
      IsAffine V.left ∧
        ∃ eV : ι → (geometricNeighborhoodAlgebra R V ⊗[R] B),
          CompleteOrthogonalIdempotents eV ∧
            ∀ a, Algebra.TensorProduct.map
              (CommRingCat.toAlgHom (geometricNeighborhoodGerm φ V v))
              (AlgHom.id R B) (eV a) = e a := by
  obtain ⟨W, t, eW, heW, hmap⟩ := exists_pointed_completeOrthogonalIdempotents φ e he
  obtain ⟨V, v, j, hV, hj⟩ := geometricStalk_exists_affine_refinement
    (Spec.map (CommRingCat.ofHom φ)) W t
  let f : (geometricNeighborhoodAlgebra R W ⊗[R] B) →ₐ[R]
      (geometricNeighborhoodAlgebra R V ⊗[R] B) :=
    Algebra.TensorProduct.map (CommRingCat.toAlgHom (geometricNeighborhoodAlgebraMap R j))
      (AlgHom.id R B)
  refine ⟨V, v, hV, fun a => f (eW a), heW.map f.toRingHom, ?_⟩
  intro a
  change ((Algebra.TensorProduct.map
    (CommRingCat.toAlgHom (geometricNeighborhoodGerm φ V v))
    (AlgHom.id R B)).comp f) (eW a) = e a
  change ((Algebra.TensorProduct.map
    (CommRingCat.toAlgHom (geometricNeighborhoodGerm φ V v))
    (AlgHom.id R B)).comp
      (Algebra.TensorProduct.map
        (CommRingCat.toAlgHom (geometricNeighborhoodAlgebraMap R j))
        (AlgHom.id R B))) (eW a) = e a
  have hcomp := Algebra.TensorProduct.map_comp
    (CommRingCat.toAlgHom (geometricNeighborhoodGerm φ V v))
    (CommRingCat.toAlgHom (geometricNeighborhoodAlgebraMap R j))
    (AlgHom.id R B) (AlgHom.id R B)
  rw [← hcomp, AlgHom.id_comp, ← CommRingCat.toAlgHom_comp,
    neighborhoodGerm_naturality φ j v t hj]
  exact hmap a

section Equivariant

variable {B : Type u} [CommRing B] [Algebra R B]
  {G : Type w} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B]

local instance coefficientTensorAction (A : Under R) : MulSemiringAction G (A ⊗[R] B) :=
  Inertia.baseChangeAction R A B G

omit [Finite G] in
private theorem transport_equivariant_family
    (E A C : Under R) (j : E ⟶ A) (v : A ⟶ C) (t : E ⟶ C) (hcomp : j ≫ v = t)
    {ι : Type u} [Fintype ι] (σ : G →* Equiv.Perm ι)
    (eE : ι → (E ⊗[R] B)) (eC : ι → (C ⊗[R] B))
    (heE : CompleteOrthogonalIdempotents eE)
    (hσ : ∀ (g : G) (a : ι), g • eE a = eE (σ g a))
    (hmap : ∀ a, Algebra.TensorProduct.map (CommRingCat.toAlgHom t)
      (AlgHom.id R B) (eE a) = eC a) :
    ∃ eA : ι → (A ⊗[R] B), CompleteOrthogonalIdempotents eA ∧
      (∀ (g : G) (a : ι), g • eA a = eA (σ g a)) ∧
      ∀ a, Algebra.TensorProduct.map (CommRingCat.toAlgHom v)
        (AlgHom.id R B) (eA a) = eC a := by
  let f : (E ⊗[R] B) →ₐ[R] (A ⊗[R] B) :=
    Algebra.TensorProduct.map (CommRingCat.toAlgHom j) (AlgHom.id R B)
  refine ⟨fun a => f (eE a), heE.map f.toRingHom, ?_, ?_⟩
  · intro g a
    change g • Algebra.TensorProduct.map (CommRingCat.toAlgHom j) (AlgHom.id R B) (eE a) =
      Algebra.TensorProduct.map (CommRingCat.toAlgHom j) (AlgHom.id R B) (eE (σ g a))
    rw [← Inertia.baseChangeAction_map R E B G (CommRingCat.toAlgHom j), hσ]
  · intro a
    change ((Algebra.TensorProduct.map (CommRingCat.toAlgHom v) (AlgHom.id R B)).comp
      (Algebra.TensorProduct.map (CommRingCat.toAlgHom j) (AlgHom.id R B))) (eE a) = eC a
    rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp,
      ← CommRingCat.toAlgHom_comp, hcomp]
    exact hmap a

private theorem exists_pointed_equivariant_completeOrthogonalIdempotents
    {ι : Type u} [Fintype ι] (σ : G →* Equiv.Perm ι)
    (e : ι → ((geometricStalkSmallAlgebraCocone φ).pt ⊗[R] B))
    (he : CompleteOrthogonalIdempotents e)
    (hσ : ∀ (g : G) (a : ι), g • e a = e (σ g a)) :
    ∃ (W : (Spec R).Etale)
      (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W)
      (eW : ι → (geometricNeighborhoodAlgebra R W ⊗[R] B)),
      CompleteOrthogonalIdempotents eW ∧
        (∀ (g : G) (a : ι), g • eW a = eW (σ g a)) ∧
        ∀ a, Algebra.TensorProduct.map
          (CommRingCat.toAlgHom (geometricNeighborhoodGerm φ W t))
          (AlgHom.id R B) (eW a) = e a := by
  obtain ⟨i, eᵢ, heᵢ, hσi, hmap⟩ :=
    Inertia.exists_equivariant_completeOrthogonalIdempotents_stage_of_filteredColimit
      (geometricStalkSmallAlgebraDiagram φ) (geometricStalkSmallAlgebraCocone φ)
      (geometricStalkSmallAlgebraCoconeIsColimit φ) σ e he hσ
  let j := (FinallySmall.fromFilteredFinalModel
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.Elementsᵒᵖ).obj i
  exact ⟨j.unop.obj, j.unop.val, eᵢ, heᵢ, hσi, hmap⟩

/-- A finite complete family in the actual geometric-stalk base change,
with a prescribed finite-group permutation action, descends to an actual
affine pointed étale neighborhood with the same group equations and the
same literal germ images. The acted-on algebra is arbitrary. -/
theorem geometricStalk_exists_affine_equivariant_completeOrthogonalIdempotents
    {ι : Type u} [Fintype ι] (σ : G →* Equiv.Perm ι)
    (e : ι → ((geometricStalkSmallAlgebraCocone φ).pt ⊗[R] B))
    (he : CompleteOrthogonalIdempotents e)
    (hσ : ∀ (g : G) (a : ι), g • e a = e (σ g a)) :
    ∃ (V : (Spec R).Etale)
      (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj V),
      IsAffine V.left ∧
        ∃ eV : ι → (geometricNeighborhoodAlgebra R V ⊗[R] B),
          CompleteOrthogonalIdempotents eV ∧
            (∀ (g : G) (a : ι), g • eV a = eV (σ g a)) ∧
            ∀ a, Algebra.TensorProduct.map
              (CommRingCat.toAlgHom (geometricNeighborhoodGerm φ V v))
              (AlgHom.id R B) (eV a) = e a := by
  obtain ⟨W, t, eW, heW, hσW, hmap⟩ :=
    exists_pointed_equivariant_completeOrthogonalIdempotents φ σ e he hσ
  obtain ⟨V, v, j, hV, hj⟩ := geometricStalk_exists_affine_refinement
    (Spec.map (CommRingCat.ofHom φ)) W t
  refine ⟨V, v, hV, ?_⟩
  exact transport_equivariant_family
    (geometricNeighborhoodAlgebra R W) (geometricNeighborhoodAlgebra R V)
    (geometricStalkSmallAlgebraCocone φ).pt
    (geometricNeighborhoodAlgebraMap R j) (geometricNeighborhoodGerm φ V v)
    (geometricNeighborhoodGerm φ W t) (neighborhoodGerm_naturality φ j v t hj)
    σ eW e heW hσW hmap

end Equivariant

end EtaleFundamentalGroups.StrictHenselian
