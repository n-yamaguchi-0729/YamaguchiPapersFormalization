/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.FlatModuleInjectiveDual
import Nyll.EtaleFundamentalGroups.Purity.InjectiveLinearDualHomology
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Tensor coefficients and linear-dual complexes

The tensor--Hom correspondence is linear and natural in the variable
complex. Consequently applying linear Hom from a coefficient module to
the dual complex agrees with dualizing the complex after tensoring with
that coefficient module. If the original terms are flat and the dual
values are injective, the dual terms are injective.
-/

noncomputable section

namespace EtaleFundamentalGroups.Purity

universe u v

open CategoryTheory Opposite MonoidalCategory
open scoped TensorProduct

variable {R : Type u} [CommRing R]

/-- The tensor--Hom correspondence with bundled module morphisms,
including its linear structure. -/
def tensorLinearDualHomEquiv (M N E : ModuleCat.{u} R) :
    (M ⟶ ModuleCat.of R (N ⟶ E)) ≃ₗ[R] (M ⊗ N ⟶ E) where
  toFun f := ModuleCat.ofHom (TensorProduct.lift f.hom₂)
  invFun g := ModuleCat.ofHom₂ (TensorProduct.curry g.hom)
  left_inv f := by
    ext m n
    rfl
  right_inv g := by
    ext m n
    rfl
  map_add' f g := by
    ext m n
    rfl
  map_smul' a f := by
    ext m n
    rfl

/-- Naturality of tensor--Hom in the contravariant module argument. -/
def tensorLinearDualHomIso (M E : ModuleCat.{u} R) :
    (linearYoneda R (ModuleCat.{u} R)).obj E ⋙
        (linearCoyoneda R (ModuleCat.{u} R)).obj (op M) ≅
      (tensorLeft M).op ⋙ (linearYoneda R (ModuleCat.{u} R)).obj E :=
  NatIso.ofComponents
    (fun N => (tensorLinearDualHomEquiv M N.unop E).toModuleIso)
    (by
      intro N N' f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro g
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro m n
      rfl)

/-- Hom from a module into a reversed dual complex is the reversed dual
of the complex with tensor coefficients. -/
def tensorLinearDualComplexIso
    (M E : ModuleCat.{u} R) {ι : Type v} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} R) c) :
    (((linearCoyoneda R (ModuleCat.{u} R)).obj (op M)).mapHomologicalComplex
        c.symm).obj (linearDualComplex E K) ≅
      linearDualComplex E ((tensorLeft M).mapHomologicalComplex c |>.obj K) :=
  (NatIso.mapHomologicalComplex (tensorLinearDualHomIso M E) c.symm).app K.op

/-- Each term of the injective-valued dual of a flat complex is injective. -/
theorem injective_linearDualComplex_X
    (E : ModuleCat.{u} R) [Module.Injective R E]
    {ι : Type v} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} R) c) (j : ι)
    [Module.Flat R (K.X j)] :
    Module.Injective R ((linearDualComplex E K).X j) := by
  let e : (K.X j ⟶ E) ≃ₗ[R] (K.X j →ₗ[R] E) :=
    ModuleCat.homLinearEquiv
  have h : Module.Injective R (K.X j →ₗ[R] E) :=
    injective_linearMap_of_flat (K.X j) E
  exact Module.Baer.injective
    (Module.Baer.of_equiv e.symm (Module.Baer.of_injective h))

end EtaleFundamentalGroups.Purity

end
