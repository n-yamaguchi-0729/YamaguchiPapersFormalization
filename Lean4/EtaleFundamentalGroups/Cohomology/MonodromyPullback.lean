/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import EtaleCohomology.Constructible.Monodromy
import EtaleCohomology.Sites.SetSheafFunctors
import EtaleFundamentalGroups.GeometricFiber.Functoriality
import Mathlib.CategoryTheory.Sites.Subcanonical

/-!
# Geometric monodromy under an actual scheme morphism

A morphism from a finite locally constant sheaf into the direct image of another
one gives a morphism between their representing finite étale covers after base
change. On geometric fibers this is equivariant for the actual homomorphism of
fundamental groups induced by the scheme morphism.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory EtaleCohomology
open scoped FintypeCatDiscrete

namespace EtaleFundamentalGroups.Cohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual Yoneda section of a sheaf morphism into a direct image gives
a morphism from the base change of its representing cover. -/
def finiteEtaleMapOfSheafPushforward (V : FiniteEtale Y) (W : FiniteEtale X)
    (α : (finiteEtaleSheaf Y).obj V ⟶
      (etaleSetPushforward f).obj ((finiteEtaleSheaf X).obj W)) :
    (FiniteEtale.pullback f).obj V ⟶ W := by
  let a : (etaleBaseChange f).obj ((finiteEtaleToEtale Y).obj V) ⟶
      (finiteEtaleToEtale X).obj W := Y.smallEtaleTopology.yonedaEquiv α
  exact MorphismProperty.Over.homMk a.hom.left (Over.w a.hom)

private theorem finiteEtaleMapOfSheafPushforward_naturality
    (V : FiniteEtale Y) (W : FiniteEtale X)
    (α : (finiteEtaleSheaf Y).obj V ⟶
      (etaleSetPushforward f).obj ((finiteEtaleSheaf X).obj W))
    (v : V ⟶ V) (w : W ⟶ W)
    (h : (finiteEtaleSheaf Y).map v ≫ α =
      α ≫ (etaleSetPushforward f).map ((finiteEtaleSheaf X).map w)) :
    (FiniteEtale.pullback f).map v ≫ finiteEtaleMapOfSheafPushforward f V W α =
      finiteEtaleMapOfSheafPushforward f V W α ≫ w := by
  have he := congrArg Y.smallEtaleTopology.yonedaEquiv h
  have hl := Y.smallEtaleTopology.yonedaEquiv_naturality α
    ((finiteEtaleToEtale Y).map v)
  have hr := Y.smallEtaleTopology.yonedaEquiv_comp α
    ((etaleSetPushforward f).map ((finiteEtaleSheaf X).map w))
  have he' := hl.trans (he.trans hr)
  apply MorphismProperty.Comma.Hom.ext'
  apply Over.OverMorphism.ext
  exact congrArg (fun a => a.hom.left) he'

/-- The representing-cover morphism associated to a map of actual sheaves. -/
def finiteLocallyConstantRepresenterPullbackMap
    (F : EtaleFiniteLocallyConstantSetSheaf Y)
    (G : EtaleFiniteLocallyConstantSetSheaf X)
    (α : F.obj ⟶ (etaleSetPushforward f).obj G.obj) :
    (FiniteEtale.pullback f).obj
        ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj F) ⟶
      (finiteEtaleEquivFiniteLocallyConstantSetSheaf X).inverse.obj G :=
  finiteEtaleMapOfSheafPushforward f _ _
    (((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).counitIso.hom.app F).hom ≫
      α ≫ (etaleSetPushforward f).map
        ((finiteEtaleEquivFiniteLocallyConstantSetSheaf X).counitIso.inv.app G).hom)

private theorem finiteLocallyConstantRepresenterPullbackMap_naturality
    (F : EtaleFiniteLocallyConstantSetSheaf Y)
    (G : EtaleFiniteLocallyConstantSetSheaf X)
    (α : F.obj ⟶ (etaleSetPushforward f).obj G.obj)
    (a : F ⟶ F) (b : G ⟶ G)
    (h : a.hom ≫ α = α ≫ (etaleSetPushforward f).map b.hom) :
    (FiniteEtale.pullback f).map
        ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.map a) ≫
      finiteLocallyConstantRepresenterPullbackMap f F G α =
    finiteLocallyConstantRepresenterPullbackMap f F G α ≫
      (finiteEtaleEquivFiniteLocallyConstantSetSheaf X).inverse.map b := by
  let eY := finiteEtaleEquivFiniteLocallyConstantSetSheaf Y
  let eX := finiteEtaleEquivFiniteLocallyConstantSetSheaf X
  let R := etaleSetPushforward f
  let c : (finiteEtaleSheaf Y).obj (eY.inverse.obj F) ⟶ F.obj :=
    (eY.counitIso.hom.app F).hom
  let d : G.obj ⟶ (finiteEtaleSheaf X).obj (eX.inverse.obj G) :=
    (eX.counitIso.inv.app G).hom
  have ha : (finiteEtaleSheaf Y).map (eY.inverse.map a) ≫ c = c ≫ a.hom :=
    congrArg (fun m => m.hom) (eY.counitIso.hom.naturality a)
  have hb : b.hom ≫ d = d ≫ (finiteEtaleSheaf X).map (eX.inverse.map b) :=
    congrArg (fun m => m.hom) (eX.counitIso.inv.naturality b)
  apply finiteEtaleMapOfSheafPushforward_naturality
  change (finiteEtaleSheaf Y).map (eY.inverse.map a) ≫ (c ≫ α ≫ R.map d) =
    (c ≫ α ≫ R.map d) ≫ R.map ((finiteEtaleSheaf X).map (eX.inverse.map b))
  have hbR := congrArg (fun k => R.map k) hb
  rw [Functor.map_comp, Functor.map_comp] at hbR
  simp only [Category.assoc]
  rw [← Category.assoc ((finiteEtaleSheaf Y).map (eY.inverse.map a)) c,
    ha, Category.assoc, ← Category.assoc a.hom α, h, Category.assoc, hbR]

variable [ConnectedSpace X] [ConnectedSpace Y]

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- The geometric-fiber map uses the canonical base-change fiber comparison
and the actual morphism of finite étale representers. -/
def finiteLocallyConstantMonodromyPullbackMap
    (F : EtaleFiniteLocallyConstantSetSheaf Y)
    (G : EtaleFiniteLocallyConstantSetSheaf X)
    (α : F.obj ⟶ (etaleSetPushforward f).obj G.obj) :
    ((finiteLocallyConstantSetMonodromy (ξ ≫ f)).functor.obj F).obj.V →
      ((finiteLocallyConstantSetMonodromy ξ).functor.obj G).obj.V :=
  fun x => (FiniteEtale.fiber ξ).map
    (finiteLocallyConstantRepresenterPullbackMap f F G α)
      ((FiniteEtale.pullbackFiberIso f ξ).inv.app
        ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj F) x)

/-- The geometric map commutes with the fundamental group action through
the actual induced homomorphism of geometric fiber functors. -/
theorem finiteLocallyConstantMonodromyPullbackMap_smul
    (F : EtaleFiniteLocallyConstantSetSheaf Y)
    (G : EtaleFiniteLocallyConstantSetSheaf X)
    (α : F.obj ⟶ (etaleSetPushforward f).obj G.obj)
    (g : Aut (FiniteEtale.fiber ξ))
    (x : ((finiteLocallyConstantSetMonodromy (ξ ≫ f)).functor.obj F).obj.V) :
    finiteLocallyConstantMonodromyPullbackMap f ξ F G α
        ((FiniteEtale.fundamentalGroupHom f ξ g) • x) =
      g • finiteLocallyConstantMonodromyPullbackMap f ξ F G α x := by
  let V := (finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj F
  let W := (finiteEtaleEquivFiniteLocallyConstantSetSheaf X).inverse.obj G
  let m : (FiniteEtale.pullback f).obj V ⟶ W :=
    finiteLocallyConstantRepresenterPullbackMap f F G α
  let t := FiniteEtale.pullbackFiberIso f ξ
  change (FiniteEtale.fiber ξ).map m
      (t.inv.app V (t.hom.app V (g.hom.app ((FiniteEtale.pullback f).obj V)
        (t.inv.app V x)))) =
    g.hom.app W ((FiniteEtale.fiber ξ).map m (t.inv.app V x))
  exact (congrArg ((FiniteEtale.fiber ξ).map m)
    (FintypeCat.hom_inv_id_apply (t.app V)
      (g.hom.app ((FiniteEtale.pullback f).obj V) (t.inv.app V x)))).trans
        (ConcreteCategory.congr_hom (g.hom.naturality m) (t.inv.app V x)).symm

/-- A commuting diagram of actual sheaves remains a commuting diagram on
geometric monodromy after the scheme pullback. -/
theorem finiteLocallyConstantMonodromyPullbackMap_naturality
    (F : EtaleFiniteLocallyConstantSetSheaf Y)
    (G : EtaleFiniteLocallyConstantSetSheaf X)
    (α : F.obj ⟶ (etaleSetPushforward f).obj G.obj)
    (a : F ⟶ F) (b : G ⟶ G)
    (h : a.hom ≫ α = α ≫ (etaleSetPushforward f).map b.hom)
    (x : ((finiteLocallyConstantSetMonodromy (ξ ≫ f)).functor.obj F).obj.V) :
    finiteLocallyConstantMonodromyPullbackMap f ξ F G α
        (((finiteLocallyConstantSetMonodromy (ξ ≫ f)).functor.map a).hom.hom x) =
      ((finiteLocallyConstantSetMonodromy ξ).functor.map b).hom.hom
        (finiteLocallyConstantMonodromyPullbackMap f ξ F G α x) := by
  let V := (finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj F
  let W := (finiteEtaleEquivFiniteLocallyConstantSetSheaf X).inverse.obj G
  let v : V ⟶ V := (finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.map a
  let w : W ⟶ W := (finiteEtaleEquivFiniteLocallyConstantSetSheaf X).inverse.map b
  let m := finiteLocallyConstantRepresenterPullbackMap f F G α
  let t := FiniteEtale.pullbackFiberIso f ξ
  have hm := congrArg (fun k => (FiniteEtale.fiber ξ).map k)
    (finiteLocallyConstantRepresenterPullbackMap_naturality f F G α a b h)
  rw [Functor.map_comp, Functor.map_comp] at hm
  have ht := ConcreteCategory.congr_hom (t.inv.naturality v) x
  change (FiniteEtale.fiber ξ).map m
      (t.inv.app V ((FiniteEtale.fiber (ξ ≫ f)).map v x)) =
    (FiniteEtale.fiber ξ).map w ((FiniteEtale.fiber ξ).map m (t.inv.app V x))
  exact (congrArg ((FiniteEtale.fiber ξ).map m) ht).trans
    (ConcreteCategory.congr_hom hm (t.inv.app V x))

end EtaleFundamentalGroups.Cohomology
