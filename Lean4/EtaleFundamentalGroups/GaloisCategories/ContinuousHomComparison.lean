/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import EtaleFundamentalGroups.GaloisCategories.FunctorFromHom
public import EtaleFundamentalGroups.GaloisCategories.Functoriality

/-!
# Recovering continuous homomorphisms from induced functors

The chosen inverse to the finite continuous-action equivalence supplies a
canonical comparison isomorphism for the functor induced by a continuous
homomorphism.  The equivariance of the chosen counit shows that the resulting
homomorphism on automorphism groups is the original one.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w

noncomputable section

open CategoryTheory
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
variable {C' : Type v₁} [Category.{v₂} C'] [GaloisCategory C']
variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
variable (F' : C' ⥤ FintypeCat.{w}) [FiberFunctor F']

/--
The canonical comparison between the composite fiber functor of the functor
induced by `h` and the original fiber functor.
-/
@[stacks 0BN5 "comparing the induced functor with the original fiber functor"]
noncomputable def comparisonIsoOfContinuousHom
    (h : Aut F' →ₜ* Aut F) :
    functorOfContinuousHom F F' h ⋙ F' ≅ F :=
  NatIso.ofComponents
    (fun X ↦
      (forget₂ (ContAction FintypeCat.{w} (Aut F')) FintypeCat).mapIso
        ((functorToContAction F').asEquivalence.counitIso.app
          ((ContAction.res FintypeCat h).obj
            ((functorToContAction F).obj X))))
    (fun f ↦ by
      let m := (ContAction.res FintypeCat h).map
        ((functorToContAction F).map f)
      exact congrArg
        (fun k ↦
          (forget₂ (ContAction FintypeCat.{w} (Aut F')) FintypeCat).map k)
        ((functorToContAction F').asEquivalence.counitIso.hom.naturality m))

omit [GaloisCategory C] [FiberFunctor F] in
/--
The canonical comparison isomorphism recovers the continuous homomorphism
from which the functor was constructed.
-/
@[stacks 0BN5 "recovering a continuous homomorphism from its induced functor"]
theorem autHomOfCompIso_comparisonIsoOfContinuousHom
    (h : Aut F' →ₜ* Aut F) :
    autHomOfCompIso (functorOfContinuousHom F F' h)
        (comparisonIsoOfContinuousHom F F' h) =
      h := by
  ext a X x
  rw [autHomOfCompIso_apply]
  let Y := (ContAction.res FintypeCat h).obj
    ((functorToContAction F).obj X)
  let e := (functorToContAction F').asEquivalence.counitIso.app Y
  change
    (ConcreteCategory.hom e.hom.hom.hom)
        ((ConcreteCategory.hom
          (a.hom.app ((functorToContAction F').asEquivalence.inverse.obj Y)))
            ((ConcreteCategory.hom e.inv.hom.hom) x)) =
      (ConcreteCategory.hom ((h a).hom.app X)) x
  have hc := ConcreteCategory.congr_hom (e.hom.hom.comm a)
    (ConcreteCategory.hom e.inv.hom.hom x)
  change
    (ConcreteCategory.hom e.hom.hom.hom)
        ((ConcreteCategory.hom
          (a.hom.app ((functorToContAction F').asEquivalence.inverse.obj Y)))
            ((ConcreteCategory.hom e.inv.hom.hom) x)) =
      (ConcreteCategory.hom ((h a).hom.app X))
        ((ConcreteCategory.hom e.hom.hom.hom)
          ((ConcreteCategory.hom e.inv.hom.hom) x)) at hc
  have heq :
      (ConcreteCategory.hom e.hom.hom.hom)
          ((ConcreteCategory.hom e.inv.hom.hom) x) = x := by
    have he := congrArg
      (fun k ↦
        (forget₂ (ContAction FintypeCat.{w} (Aut F')) FintypeCat).map k)
      e.inv_hom_id
    exact ConcreteCategory.congr_hom he x
  exact hc.trans
    (congrArg (ConcreteCategory.hom ((h a).hom.app X)) heq)

end CategoryTheory.PreGaloisCategory
