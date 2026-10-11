/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
import Nyll.EtaleCohomology.Sites.EtaleRestriction
import Nyll.EtaleCohomology.Sites.EtaleSlice
import Nyll.SchemeTheory.WeilRestriction.LocalRepresenters
import Nyll.SchemeTheory.WeilRestriction.LocalRepresenterDiagram
import Nyll.SchemeTheory.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Gluing finite étale local representers on a directed open cover

The actual representing equivalences on the small étale sites determine all
transition maps and their cartesian squares. Relative gluing then constructs
a finite étale scheme on the whole base, whose restrictions are the chosen
local schemes. No gluing comparisons or cocycle laws are assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits SchemeTheory.WeilRestriction

universe u v

namespace EtaleCohomology

variable {X : Scheme.{u}} (G : Sheaf X.smallEtaleTopology (Type u))
  (𝒰 : X.OpenCover) [Category.{v} 𝒰.I₀] [𝒰.LocallyDirected]

/-- Regard the directed open cover as a diagram in the base's small étale category. -/
def etaleOpenCoverDiagram : 𝒰.I₀ ⥤ X.Etale :=
  MorphismProperty.Comma.lift
    (Over.lift 𝒰.functorOfLocallyDirected 𝒰.functorOfLocallyDirectedHomBase)
    (fun i => show Etale (𝒰.f i) from inferInstance) (fun _ => trivial) (fun _ => trivial)

variable (W : ∀ i : 𝒰.I₀, FiniteEtale (𝒰.X i))
  (h : ∀ i : 𝒰.I₀, ((etalePostcompose (𝒰.f i)).op ⋙ G.obj).RepresentableBy
    ((finiteEtaleToEtale (𝒰.X i)).obj (W i)))

/-- Ordinary local representations give actual relative gluing data via the
slice equivalences of the small étale category. -/
def etaleLocalRepresenterGluingData : 𝒰.RelativeGluingData := by
  let D : 𝒰.I₀ ⥤ X.Etale := etaleOpenCoverDiagram 𝒰
  let W' : ∀ i : 𝒰.I₀, Over (D.obj i) := fun i =>
    (etaleSliceEquiv (D.obj i)).inverse.obj ((finiteEtaleToEtale (𝒰.X i)).obj (W i))
  let h' : ∀ i : 𝒰.I₀, (sliceRestriction G.obj (D.obj i)).RepresentableBy (W' i) :=
    fun i => representableByEtaleSlice (D.obj i) G.obj
      ((finiteEtaleToEtale (𝒰.X i)).obj (W i)) (h i)
  let H : X.Etale ⥤ Scheme.{u} := Scheme.Etale.forget X ⋙ Over.forget X
  exact
    { functor := localRepresenterDiagram G.obj D W' h' ⋙ H
      natTrans := Functor.whiskerRight (localRepresenterProjection G.obj D W' h') H
      equifibered := (localRepresenterProjection_equifibered G.obj D W' h').whiskerRight H }

/-- The local structural maps of the gluing data are the original finite étale maps. -/
lemma etaleLocalRepresenterGluingData_app (i : 𝒰.I₀) :
    (etaleLocalRepresenterGluingData G 𝒰 W h).natTrans.app i = (W i).hom := rfl

variable [Quiver.IsThin 𝒰.I₀] [Small.{u} 𝒰.I₀]

/-- The actual glued morphism is finite étale, by its cartesian local models. -/
lemma etaleLocalRepresenterGluingData_isFiniteEtale :
    IsFiniteEtale (etaleLocalRepresenterGluingData G 𝒰 W h).toBase := by
  let d := etaleLocalRepresenterGluingData G 𝒰 W h
  let P : MorphismProperty Scheme.{u} := @IsFiniteEtale
  change P d.toBase
  apply IsZariskiLocalAtTarget.of_openCover 𝒰
  intro i
  change P (pullback.snd d.toBase (𝒰.f i))
  let e := (d.isPullback_natTrans_ι_toBase i).flip.isoPullback
  have he : e.hom ≫ pullback.snd d.toBase (𝒰.f i) = d.natTrans.app i :=
    (d.isPullback_natTrans_ι_toBase i).flip.isoPullback_hom_snd
  exact (P.cancel_left_of_respectsIso e.hom (pullback.snd d.toBase (𝒰.f i))).mp
    (he.symm ▸ (show P (d.natTrans.app i) from (W i).prop))

/-- The finite étale scheme obtained by gluing the given local representers. -/
def etaleGluedLocalRepresenter : FiniteEtale X :=
  MorphismProperty.Over.mk ⊤ (etaleLocalRepresenterGluingData G 𝒰 W h).toBase
    (etaleLocalRepresenterGluingData_isFiniteEtale G 𝒰 W h)

/-- Each original local representer is the genuine pullback of the glued scheme. -/
lemma etaleGluedLocalRepresenter_isPullback (i : 𝒰.I₀) :
    IsPullback (W i).hom
      (colimit.ι (etaleLocalRepresenterGluingData G 𝒰 W h).functor i)
      (𝒰.f i) (etaleGluedLocalRepresenter G 𝒰 W h).hom :=
  (etaleLocalRepresenterGluingData G 𝒰 W h).isPullback_natTrans_ι_toBase i

end EtaleCohomology
