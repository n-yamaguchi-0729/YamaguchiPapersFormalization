/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality
import EtaleFundamentalGroups.GeometricFiber.FiniteGaloisSets
import EtaleFundamentalGroups.GaloisCategories.FiberFunctorComparison
import EtaleFundamentalGroups.GaloisCategories.FiberIso
import Mathlib.CategoryTheory.Galois.Prorepresentability
import Mathlib.FieldTheory.IsSepClosed

/-!
# The absolute Galois group at an algebraic-closure geometric point

An extension of separably closed fields induces a canonical map of geometric
fiber functors by precomposition on geometric points. This map is invertible:
after comparison with any isomorphism of fiber functors, it is an endomorphism
of a fiber functor, and every such endomorphism is invertible.

Applying this to the separable closure inside the algebraic closure identifies
the absolute Galois group with the fundamental group at the algebraic-closure
point. The finite-action equivalence respects both this group isomorphism and
the forgetful functor to the geometric fiber.
-/


noncomputable section

universe u

open CategoryTheory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

variable (k K Ω : Type u) [Field k] [Field K] [Field Ω]
  [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]

section Extension

variable [IsSepClosed K] [IsSepClosed Ω]

private def fieldPointExtension : Over.mk (ξ k Ω) ⟶ Over.mk (ξ k K) :=
  Over.homMk (ξ K Ω) (fieldGeometricPoint_comp k K Ω)

/-- Extension of the geometric-point field, defined by precomposition on points. -/
def fieldFiberExtension : fib k K ⟶ fib k Ω where
  app X := FintypeCat.homMk fun x ↦
    (fiberObjEquivHom (ξ k Ω) X).symm
      (fieldPointExtension k K Ω ≫ fiberObjEquivHom (ξ k K) X x)
  naturality X Y f := by
    apply FintypeCat.hom_ext
    intro x
    change (fiberObjEquivHom (ξ k Ω) Y).symm
        (fieldPointExtension k K Ω ≫
          fiberObjEquivHom (ξ k K) Y ((fib k K).map f x)) =
      (fib k Ω).map f ((fiberObjEquivHom (ξ k Ω) X).symm
        (fieldPointExtension k K Ω ≫ fiberObjEquivHom (ξ k K) X x))
    rw [fiberObjEquivHom_symm_naturality,
      ← fiberObjEquivHom_naturality (ξ k K) f x, Category.assoc]

private lemma fieldFiberExtension_isIso : IsIso (fieldFiberExtension k K Ω) := by
  obtain ⟨e⟩ := PreGaloisCategory.nonempty_iso_of_exact (fib k K) (fib k Ω)
  let : IsIso (fieldFiberExtension k K Ω ≫ e.inv) :=
    PreGaloisCategory.FibreFunctor.end_isIso (fib k K)
      (fieldFiberExtension k K Ω ≫ e.inv)
  exact IsIso.of_isIso_comp_right (fieldFiberExtension k K Ω) e.inv

/-- Extending a separably closed geometric-point field preserves the fiber functor. -/
def fieldFiberExtensionIso : fib k K ≅ fib k Ω := by
  letI : IsIso (fieldFiberExtension k K Ω) := fieldFiberExtension_isIso k K Ω
  exact asIso (fieldFiberExtension k K Ω)

/-- The canonical comparison sends a geometric point to its composite with the field extension. -/
lemma fieldFiberExtensionIso_point (X : FiniteEtale (Spec (.of k)))
    (x : (fib k K).obj X) :
    (fiberObjEquivHom (ξ k Ω) X ((fieldFiberExtensionIso k K Ω).hom.app X x)).left =
      ξ K Ω ≫ (fiberObjEquivHom (ξ k K) X x).left := by
  change (fiberObjEquivHom (ξ k Ω) X
    ((fiberObjEquivHom (ξ k Ω) X).symm
      (fieldPointExtension k K Ω ≫ fiberObjEquivHom (ξ k K) X x))).left = _
  rw [Equiv.apply_symm_apply]
  rfl

end Extension

section AbsoluteGalois

variable [IsSepClosure k K] [IsSepClosed Ω]

attribute [local instance] IsSepClosure.sep_closed

private def absoluteGaloisToSeparableFiberAut : (K ≃ₐ[k] K) ≃ₜ* Aut (fib k K) :=
  ContinuousMulEquiv.mk'
    (PreGaloisCategory.toAutHomeo (fib k K) (K ≃ₐ[k] K))
    (fun g h ↦ by
      simpa only [PreGaloisCategory.toAutHomeo_apply] using
        (PreGaloisCategory.toAut (fib k K) (K ≃ₐ[k] K)).map_mul g h)

/-- The absolute Galois group acts as all automorphisms of the extended geometric fiber. -/
def absoluteGaloisToExtendedFiberAut : (K ≃ₐ[k] K) ≃ₜ* Aut (fib k Ω) :=
  (absoluteGaloisToSeparableFiberAut k K).trans
    (PreGaloisCategory.continuousConjAut (fieldFiberExtensionIso k K Ω))

/-- The finite Galois-set equivalence agrees with the equivalence at the extended point. -/
def equivContActionExtendedFiberIso :
    (equivContAction k K).functor ≅
      PreGaloisCategory.functorToContAction (fib k Ω) ⋙
        (ContAction.resEquiv FintypeCat (absoluteGaloisToExtendedFiberAut k K Ω)).functor := by
  let e : (K ≃ₐ[k] K) ≃ₜ* Aut (fib k K) := absoluteGaloisToSeparableFiberAut k K
  let t : Aut (fib k K) ≃ₜ* Aut (fib k Ω) :=
    PreGaloisCategory.continuousConjAut (fieldFiberExtensionIso k K Ω)
  let er : (K ≃ₐ[k] K) →ₜ* Aut (fib k K) :=
    ContinuousMonoidHom.toContinuousMonoidHom e
  let tr : Aut (fib k K) →ₜ* Aut (fib k Ω) :=
    ContinuousMonoidHom.toContinuousMonoidHom t
  let step₁ :=
    Functor.isoWhiskerRight
      (PreGaloisCategory.functorToContActionFiberIso (fieldFiberExtensionIso k K Ω))
      (ContAction.res FintypeCat er)
  let step₂ :=
    Functor.associator (PreGaloisCategory.functorToContAction (fib k Ω))
      (ContAction.res FintypeCat tr)
      (ContAction.res FintypeCat er)
  let step₃ :=
    Functor.isoWhiskerLeft (PreGaloisCategory.functorToContAction (fib k Ω))
      (ContAction.resComp FintypeCat er tr).symm
  exact step₁.trans (step₂.trans step₃)

/-- Forgetting the finite Galois action gives the fiber at the extended geometric point. -/
def equivContActionExtendedFiberForgetIso :
    (equivContAction k K).functor ⋙
      forget₂ (ContAction FintypeCat.{u} (K ≃ₐ[k] K)) FintypeCat ≅ fib k Ω := by
  let e : (equivContAction k K).functor ⋙
      forget₂ (ContAction FintypeCat.{u} (K ≃ₐ[k] K)) FintypeCat ≅ fib k K :=
    NatIso.ofComponents (fun X ↦ Iso.refl ((fib k K).obj X)) (fun f ↦ by rfl)
  exact e.trans (fieldFiberExtensionIso k K Ω)

end AbsoluteGalois

/-- **Stacks Project, Tag 0BNE.** The absolute Galois group is the étale fundamental
group of the field, based at its algebraic closure. -/
@[stacks 0BNE "The absolute Galois group is the fundamental group at the algebraic-closure point."]
def absoluteGaloisEquivFundamentalGroup (k : Type u) [Field k] :
    (SeparableClosure k ≃ₐ[k] SeparableClosure k) ≃ₜ* Aut (fib k (AlgebraicClosure k)) :=
  absoluteGaloisToExtendedFiberAut k (SeparableClosure k) (AlgebraicClosure k)

/-- The finite-action equivalence in Tag 0BNE commutes with the algebraic-closure fiber functor. -/
def equivContActionAlgebraicClosureForgetIso (k : Type u) [Field k] :
    (equivContAction k (SeparableClosure k)).functor ⋙
      forget₂ (ContAction FintypeCat.{u}
        (SeparableClosure k ≃ₐ[k] SeparableClosure k)) FintypeCat ≅
      fib k (AlgebraicClosure k) :=
  equivContActionExtendedFiberForgetIso k (SeparableClosure k) (AlgebraicClosure k)

end AlgebraicGeometry.FiniteEtale
