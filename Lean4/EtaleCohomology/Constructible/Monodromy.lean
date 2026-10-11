/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.FiniteEtaleSheaf
import EtaleCohomology.Constructible.FiniteLocallyConstantEquivalence
import EtaleCohomology.Constructible.FiniteLocallyConstantSet
import EtaleFundamentalGroups.FiniteEtale.GaloisCategory
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Topology.Category.FinTopCat

/-!
# Monodromy of finite locally constant étale sheaves

For a connected scheme with a geometric point, finite locally constant set
sheaves are equivalent to finite sets with a continuous action of the étale
fundamental group. The group is the existing EFG automorphism group of the
geometric fiber functor. The underlying finite set of this action is naturally
isomorphic to the actual geometric stalk, defined by the site's filtered colimit.

The Galois-category equivalence is supplied by mathlib, and the represented-sheaf
fiber comparison by `finiteEtaleSheafFiberIso`. The comparison below also uses
the counit of the constructed finite étale representability equivalence, so it
applies to every finite locally constant sheaf, not only a represented input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

universe u

namespace EtaleCohomology

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- Finite locally constant sheaves are finite continuous representations of the
étale fundamental group on sets. -/
def finiteLocallyConstantSetMonodromy :
    EtaleFiniteLocallyConstantSetSheaf X ≌ ContAction FintypeCat.{u} (Aut (FiniteEtale.fiber ξ)) :=
  (finiteEtaleEquivFiniteLocallyConstantSetSheaf X).symm.trans
    (functorToContAction (FiniteEtale.fiber ξ)).asEquivalence

/-- Forgetting the monodromy action recovers the actual geometric stalk,
naturally in every finite locally constant étale sheaf. -/
def finiteLocallyConstantSetMonodromyStalkIso :
    (finiteLocallyConstantSetMonodromy ξ).functor ⋙
        forget₂ (ContAction FintypeCat.{u} (Aut (FiniteEtale.fiber ξ))) FintypeCat ⋙
        forget FintypeCat ≅
      ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := X)) ⋙
        (Scheme.pointSmallEtale ξ).sheafFiber := by
  let e := finiteEtaleEquivFiniteLocallyConstantSetSheaf X
  let ι := ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := X))
  let Φ := (Scheme.pointSmallEtale ξ).sheafFiber (A := Type u)
  have h : e.inverse ⋙ finiteEtaleSheaf X ≅ ι :=
    (Functor.associator e.inverse e.functor ι).symm ≪≫
      Functor.isoWhiskerRight e.counitIso ι ≪≫ ι.leftUnitor
  change (e.inverse ⋙ FiniteEtale.fiber ξ) ⋙ forget FintypeCat ≅ ι ⋙ Φ
  exact Functor.associator e.inverse (FiniteEtale.fiber ξ) (forget FintypeCat) ≪≫
    Functor.isoWhiskerLeft e.inverse (finiteEtaleSheafFiberIso ξ).symm ≪≫
    (Functor.associator e.inverse (finiteEtaleSheaf X) Φ).symm ≪≫
    Functor.isoWhiskerRight h Φ

end EtaleCohomology
