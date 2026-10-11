/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantEquivalence
import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantSet
import Nyll.EtaleCohomology.Constructible.Monodromy
import Nyll.EtaleCohomology.Sites.RepresentablePullback
import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.Topology.Category.FinTopCat

/-!
# Geometric pullback of finite locally constant representers

Inverse image of the actual sheaf of a finite étale cover is the sheaf of
its scheme-theoretic base change. Consequently an arbitrary finite locally
constant sheaf pulls back to the base change of its existing representer.
These are comparisons of actual sheaves, not assumptions about monodromy.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleCohomology
open scoped FintypeCatDiscrete

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Sheaf inverse image agrees naturally with base change of finite étale covers. -/
def finiteEtaleSheafPullbackIso :
    finiteEtaleSheaf Y ⋙ etaleSetPullback f ≅
      FiniteEtale.pullback f ⋙ finiteEtaleSheaf X :=
  NatIso.ofComponents
    (fun V => etaleSetPullbackYonedaObjIso f ((finiteEtaleToEtale Y).obj V))
    (fun k => etaleSetPullbackYonedaObjIso_hom_naturality f
      ((finiteEtaleToEtale Y).map k))

/-- Actual inverse image of a finite locally constant set sheaf. -/
def finiteLocallyConstantSetPullback :
    EtaleFiniteLocallyConstantSetSheaf Y ⥤ EtaleFiniteLocallyConstantSetSheaf X where
  obj G := ⟨(etaleSetPullback f).obj G.obj, G.property.pullback f⟩
  map k := ObjectProperty.homMk ((etaleSetPullback f).map k.hom)
  map_id G := by
    apply ObjectProperty.hom_ext
    exact (etaleSetPullback f).map_id G.obj
  map_comp k l := by
    apply ObjectProperty.hom_ext
    exact (etaleSetPullback f).map_comp k.hom l.hom

/-- The inverse image of the original sheaf is represented by the actual
scheme base change of its chosen finite étale representer. -/
def finiteLocallyConstantPullbackRepresenterIso
    (G : EtaleFiniteLocallyConstantSetSheaf Y) :
    (etaleSetPullback f).obj G.obj ≅
      (finiteEtaleSheaf X).obj
        ((FiniteEtale.pullback f).obj
          ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G)) :=
  (etaleSetPullback f).mapIso
      (((ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := Y))).mapIso
        ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).counitIso.app G)).symm) ≪≫
    (finiteEtaleSheafPullbackIso f).app
      ((finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G)


/-- The comparison of representers is natural in every morphism of finite
locally constant sheaves. It follows by full faithfulness of the actual
represented-sheaf functor, rather than a chosen compatibility hypothesis. -/
def finiteLocallyConstantPullbackRepresenterNatIso :
    finiteLocallyConstantSetPullback f ⋙
        (finiteEtaleEquivFiniteLocallyConstantSetSheaf X).inverse ≅
      (finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse ⋙
        FiniteEtale.pullback f := by
  let eX := finiteEtaleEquivFiniteLocallyConstantSetSheaf X
  let eY := finiteEtaleEquivFiniteLocallyConstantSetSheaf Y
  let IX := ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := X))
  let IY := ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := Y))
  let L := finiteLocallyConstantSetPullback f
  let hX : eX.inverse ⋙ finiteEtaleSheaf X ≅ IX :=
    (Functor.associator eX.inverse eX.functor IX).symm ≪≫
      Functor.isoWhiskerRight eX.counitIso IX ≪≫ IX.leftUnitor
  let hY : eY.inverse ⋙ finiteEtaleSheaf Y ≅ IY :=
    (Functor.associator eY.inverse eY.functor IY).symm ≪≫
      Functor.isoWhiskerRight eY.counitIso IY ≪≫ IY.leftUnitor
  have : (finiteEtaleSheaf X).Full := (finiteEtaleSheafFullyFaithful X).full
  have : (finiteEtaleSheaf X).Faithful := (finiteEtaleSheafFullyFaithful X).faithful
  apply Functor.fullyFaithfulCancelRight (finiteEtaleSheaf X)
  exact Functor.associator L eX.inverse (finiteEtaleSheaf X) ≪≫
    Functor.isoWhiskerLeft L hX ≪≫
    Functor.isoWhiskerRight hY.symm (etaleSetPullback f) ≪≫
    Functor.associator eY.inverse (finiteEtaleSheaf Y) (etaleSetPullback f) ≪≫
    Functor.isoWhiskerLeft eY.inverse (finiteEtaleSheafPullbackIso f) ≪≫
    (Functor.associator eY.inverse (FiniteEtale.pullback f) (finiteEtaleSheaf X)).symm

variable [ConnectedSpace X] [ConnectedSpace Y]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- Monodromy of actual sheaf inverse image is restriction along the actual
scheme-induced homomorphism of étale fundamental groups. This is a natural
isomorphism of finite continuous representations. -/
def finiteLocallyConstantSetMonodromyPullbackIso :
    finiteLocallyConstantSetPullback f ⋙
        (finiteLocallyConstantSetMonodromy ξ).functor ≅
      (finiteLocallyConstantSetMonodromy (ξ ≫ f)).functor ⋙
        ContAction.res FintypeCat (FiniteEtale.fundamentalGroupHom f ξ) := by
  let eX := finiteEtaleEquivFiniteLocallyConstantSetSheaf X
  let eY := finiteEtaleEquivFiniteLocallyConstantSetSheaf Y
  let AX := PreGaloisCategory.functorToContAction (FiniteEtale.fiber ξ)
  let AY := PreGaloisCategory.functorToContAction (FiniteEtale.fiber (ξ ≫ f))
  let R := ContAction.res FintypeCat (FiniteEtale.fundamentalGroupHom f ξ)
  exact (Functor.associator (finiteLocallyConstantSetPullback f) eX.inverse AX).symm ≪≫
    Functor.isoWhiskerRight (finiteLocallyConstantPullbackRepresenterNatIso f) AX ≪≫
    Functor.associator eY.inverse (FiniteEtale.pullback f) AX ≪≫
    Functor.isoWhiskerLeft eY.inverse
      (PreGaloisCategory.functorToContActionCompIso
        (FiniteEtale.pullback f) (FiniteEtale.pullbackFiberIso f ξ)) ≪≫
    (Functor.associator eY.inverse AY R).symm

end EtaleFundamentalGroups.Cohomology
