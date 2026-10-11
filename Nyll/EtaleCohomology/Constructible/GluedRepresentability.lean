/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.LocalRepresenterGluing
import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
import Nyll.EtaleCohomology.Constructible.SigmaRepresenter
import Nyll.EtaleCohomology.Sites.EtaleRestriction
import Nyll.EtaleCohomology.Sites.EtaleSlice
import Nyll.EtaleCohomology.Sites.LocallyDirectedCover
import Nyll.EtaleCohomology.Sites.Subcanonical
import Nyll.SchemeTheory.FiniteEtale.Basic
import Nyll.SchemeTheory.WeilRestriction.LocalRepresenters
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Sites.Hypercover.One
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Logic.Function.Basic

/-!
# Representability by gluing on the small étale site

Local finite étale representers on a locally directed open cover have canonical
transition maps preserving their universal sections. The small-site hypercover
therefore glues those sections. Cartesian local comparisons identify the resulting
Yoneda map locally with the actual representing equivalences. The sheaf condition
then makes it an isomorphism on the whole base.

The cover may have any small index type. No affine, quasi-compact, quasi-separated,
connected, or noetherian assumption is made on the base.
-/

noncomputable section
universe u v w
open AlgebraicGeometry CategoryTheory Limits Opposite SchemeTheory.WeilRestriction

namespace EtaleCohomology

variable {X : Scheme.{u}} (G : Sheaf X.smallEtaleTopology (Type u))
  (𝒰 : Scheme.OpenCover.{w} X) [Category.{v} 𝒰.I₀] [𝒰.LocallyDirected]
  (W : ∀ i : 𝒰.I₀, FiniteEtale (𝒰.X i))
  (h : ∀ i : 𝒰.I₀, ((etalePostcompose (𝒰.f i)).op ⋙ G.obj).RepresentableBy
    ((finiteEtaleToEtale (𝒰.X i)).obj (W i)))
  [Quiver.IsThin 𝒰.I₀] [Small.{u} 𝒰.I₀]

/-- The canonical inclusion of a local representer into the glued finite étale scheme. -/
def etaleGluedRepresenterInclusion (i : 𝒰.I₀) :
    (etalePostcompose (𝒰.f i)).obj ((finiteEtaleToEtale (𝒰.X i)).obj (W i)) ⟶
      (finiteEtaleToEtale X).obj (etaleGluedLocalRepresenter G 𝒰 W h) :=
  MorphismProperty.Over.homMk
    (colimit.ι (etaleLocalRepresenterGluingData G 𝒰 W h).functor i)
    ((etaleLocalRepresenterGluingData G 𝒰 W h).ι_toBase i)

/-- The universal element of the actual slice representation on a cover member. -/
def etaleLocalUniversalSection (i : 𝒰.I₀) :
    G.obj.obj (op ((etalePostcompose (𝒰.f i)).obj
      ((finiteEtaleToEtale (𝒰.X i)).obj (W i)))) :=
  (representableByEtaleSlice ((etaleOpenCoverDiagram 𝒰).obj i) G.obj
    ((finiteEtaleToEtale (𝒰.X i)).obj (W i)) (h i)).homEquiv (𝟙 _)

/-- The local representers cover the glued object in the small étale site. -/
def etaleGluedRepresenterHypercover :
    X.smallEtaleTopology.OneHypercover.{max v w}
      ((finiteEtaleToEtale X).obj (etaleGluedLocalRepresenter G 𝒰 W h)) :=
  let d : 𝒰.RelativeGluingData := etaleLocalRepresenterGluingData G 𝒰 W h
  Sites.locallyDirectedOpenCoverHypercover.{u, v, w}
    ((finiteEtaleToEtale X).obj (etaleGluedLocalRepresenter G 𝒰 W h)) d.cover
    (h𝒰 := by change d.cover.LocallyDirected; infer_instance)
    (fun i => (W i).hom ≫ 𝒰.f i) (fun i => d.ι_toBase i)

/-- Canonical transitions preserve the universal elements, making them compatible. -/
def etaleGluedRepresenterCompatibleSections :
    ((etaleGluedRepresenterHypercover G 𝒰 W h).multicospanIndex G.obj).sections := by
  let D := etaleOpenCoverDiagram 𝒰
  let W' : ∀ i : 𝒰.I₀, Over (D.obj i) := fun i =>
    (etaleSliceEquiv (D.obj i)).inverse.obj ((finiteEtaleToEtale (𝒰.X i)).obj (W i))
  let h' : ∀ i : 𝒰.I₀, (sliceRestriction G.obj (D.obj i)).RepresentableBy (W' i) :=
    fun i => representableByEtaleSlice (D.obj i) G.obj
      ((finiteEtaleToEtale (𝒰.X i)).obj (W i)) (h i)
  refine { val := fun i => etaleLocalUniversalSection G 𝒰 W h i.down
           property := ?_ }
  rintro ⟨⟨i, j⟩, ⟨k, a, b⟩⟩
  change G.obj.map (localRepresenterMap (h' k) (h' i.down) (D.map a)).op
      ((h' i.down).homEquiv (𝟙 (W' i.down))) =
    G.obj.map (localRepresenterMap (h' k) (h' j.down) (D.map b)).op
      ((h' j.down).homEquiv (𝟙 (W' j.down)))
  exact (localRepresenterMap_universal (h' k) (h' i.down) (D.map a)).trans
    (localRepresenterMap_universal (h' k) (h' j.down) (D.map b)).symm

/-- The actual sheaf condition glues the local universal elements to a global section. -/
def etaleGluedRepresenterUniversalSection :
    G.obj.obj (op ((finiteEtaleToEtale X).obj (etaleGluedLocalRepresenter G 𝒰 W h))) :=
  Multifork.IsLimit.sectionsEquiv
    ((etaleGluedRepresenterHypercover G 𝒰 W h).isLimitMultifork G)
    (etaleGluedRepresenterCompatibleSections G 𝒰 W h)

/-- Restriction of the glued section recovers each local universal element. -/
lemma etaleGluedRepresenterUniversalSection_restrict (i : 𝒰.I₀) :
    G.obj.map (etaleGluedRepresenterInclusion G 𝒰 W h i).op
        (etaleGluedRepresenterUniversalSection G 𝒰 W h) =
      etaleLocalUniversalSection G 𝒰 W h i :=
  Multifork.IsLimit.sectionsEquiv_apply_val
    ((etaleGluedRepresenterHypercover G 𝒰 W h).isLimitMultifork G)
    (etaleGluedRepresenterCompatibleSections G 𝒰 W h) (ULift.up i)

/-- A sheaf with finite étale local representers is represented by their glued scheme. -/
def etaleGluedLocalRepresentable :
    G.obj.RepresentableBy ((finiteEtaleToEtale X).obj (etaleGluedLocalRepresenter G 𝒰 W h)) := by
  let Z := (finiteEtaleToEtale X).obj (etaleGluedLocalRepresenter G 𝒰 W h)
  let s := etaleGluedRepresenterUniversalSection G 𝒰 W h
  let η : X.smallEtaleTopology.yoneda.obj Z ⟶ G := X.smallEtaleTopology.yonedaEquiv.symm s
  have hη : IsIso η := by
    let 𝒱 := 𝒰.changeProp (Q := show MorphismProperty Scheme.{u} from @Etale)
      (fun i => show Etale (𝒰.f i) from inferInstance)
    apply isIso_of_bijective_on_etaleCover 𝒱 η
    intro i T
    have : Etale (𝒰.f i) := ((etaleOpenCoverDiagram 𝒰).obj i).prop
    let V := (finiteEtaleToEtale (𝒰.X i)).obj (W i)
    let q := etaleGluedRepresenterInclusion G 𝒰 W h i
    have hHom := etalePostcompose_hom_bijective_of_isPullback (𝒰.f i) V Z q
      (etaleGluedLocalRepresenter_isPullback G 𝒰 W h i) T
    apply (Function.Bijective.of_comp_iff _ hHom).mp
    let E := etaleSliceEquiv ((etaleOpenCoverDiagram 𝒰).obj i)
    let hi := representableByEtaleSlice ((etaleOpenCoverDiagram 𝒰).obj i) G.obj V (h i)
    let e : (T ⟶ V) ≃ G.obj.obj (op ((etalePostcompose (𝒰.f i)).obj T)) :=
      (E.symm.fullyFaithfulFunctor.homEquiv (X := T) (Y := V)).trans hi.homEquiv
    have heq : (fun g : T ⟶ V =>
        η.hom.app (op ((etalePostcompose (𝒰.f i)).obj T))
          ((etalePostcompose (𝒰.f i)).map g ≫ q)) = e := by
      funext g
      change G.obj.map ((etalePostcompose (𝒰.f i)).map g ≫ q).op s = _
      rw [op_comp, G.obj.map_comp]
      change G.obj.map ((etalePostcompose (𝒰.f i)).map g).op
        (G.obj.map q.op s) = _
      exact (congrArg (fun t => G.obj.map ((etalePostcompose (𝒰.f i)).map g).op t)
        (etaleGluedRepresenterUniversalSection_restrict G 𝒰 W h i)).trans
          (hi.homEquiv_eq (E.inverse.map g)).symm
    change Function.Bijective (fun g : T ⟶ V =>
      η.hom.app (op ((etalePostcompose (𝒰.f i)).obj T))
        ((etalePostcompose (𝒰.f i)).map g ≫ q))
    rw [heq]
    exact e.bijective
  exact Functor.representableByEquiv.symm
    ((sheafToPresheaf X.smallEtaleTopology (Type u)).mapIso (asIso η))

end EtaleCohomology
