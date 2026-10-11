/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.RepresenterAction
import EtaleCohomology.Constructible.SigmaRepresenter
import EtaleCohomology.Sites.EtaleRestriction
import EtaleCohomology.Sites.Subcanonical
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Yoneda

/-!
# Identifying a descended scheme with the original sheaf

A cartesian local representer descends to a representer of the original
sheaf when its projection is invariant under the actual descent action.
The proof glues the universal section along a surjective étale morphism,
then checks the resulting Yoneda map on the cover.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

lemma isSheafFor_surjective_etaleHom {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (Type u)) {U V : X.Etale}
    (q : U ⟶ V) [Surjective q.left] :
    Presieve.IsSheafFor G.obj (Presieve.singleton q) := by
  apply (Presieve.isSheafFor_iff_generate _).mpr
  apply G.property.isSheafFor
  have hc : Sieve.ofArrows (fun _ : PUnit.{1} => U) (fun _ => q) ∈
      X.smallEtaleTopology V := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    rw [Set.iUnion_const]
    exact Set.range_eq_univ.mpr q.left.surjective
  simpa only [Sieve.ofArrows, Presieve.ofArrows_pUnit] using hc

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
variable (G : Sheaf X.smallEtaleTopology (Type u)) (W : Y.Etale)
variable (h : ((etalePostcompose f).op ⋙ G.obj).RepresentableBy W)
variable (Z : X.Etale) (q : (etalePostcompose f).obj W ⟶ Z)
variable (hcart : IsPullback W.hom q.left f Z.hom)
variable (hact : representerAction f G W h ≫ q.left =
  pullback.snd f (W.hom ≫ f) ≫ q.left)

include hcart hact

/-- The quotient's invariance makes the local universal section compatible
on every pair of arrows over the proposed descended scheme. -/
lemma representerSection_compatible {T : X.Etale}
    (a b : T ⟶ (etalePostcompose f).obj W) (hab : a ≫ q = b ≫ q) :
    G.obj.map a.op (representerSection f G W h) =
      G.obj.map b.op (representerSection f G W h) := by
  have habase : (a.left ≫ W.hom) ≫ f = b.left ≫ (W.hom ≫ f) := by
    exact (Category.assoc a.left W.hom f).trans (a.w.trans b.w.symm)
  let r : T ⟶ (etalePostcompose f).obj (representerActionDomain f W) :=
    MorphismProperty.Over.homMk
      (pullback.lift (f := f) (g := W.hom ≫ f) (a.left ≫ W.hom) b.left habase)
      ((pullback.lift_fst_assoc _ _ _ f).trans
        ((Category.assoc a.left W.hom f).trans a.w)) trivial
  have hr : r.left ≫ representerAction f G W h = a.left := by
    apply hcart.hom_ext
    · exact (Category.assoc r.left (representerAction f G W h) W.hom).trans
        ((congrArg (fun c => r.left ≫ c) (representerAction_over f G W h)).trans
          (pullback.lift_fst _ _ _))
    · exact (Category.assoc r.left (representerAction f G W h) q.left).trans
        ((congrArg (fun c => r.left ≫ c) hact).trans
          ((Category.assoc r.left (pullback.snd f (W.hom ≫ f)) q.left).symm.trans
            ((congrArg (fun c => c ≫ q.left) (pullback.lift_snd _ _ habase)).trans
              (congrArg (fun e => e.left) hab).symm)))
  have ha : r ≫ (etalePostcompose f).map (representerActionHom f G W h) = a :=
    MorphismProperty.Over.Hom.ext hr
  have hb : r ≫ representerActionSecond f W = b :=
    MorphismProperty.Over.Hom.ext (pullback.lift_snd _ _ _)
  rw [← ha, ← hb, op_comp, op_comp, G.obj.map_comp, G.obj.map_comp]
  exact congrArg (fun s => G.obj.map r.op s) (representerAction_section f G W h)

/-- An equivariant cartesian local representer represents the original sheaf.
The universal section is descended using the actual sheaf condition. -/
def representableBy_of_cartesian_localRepresenter [Surjective f] :
    G.obj.RepresentableBy Z := by
  have : Surjective q.left :=
    (show MorphismProperty Scheme.{u} from @Surjective).of_isPullback hcart inferInstance
  have hS := (Presieve.isSheafFor_singleton (P := G.obj)).mp
    (isSheafFor_surjective_etaleHom G q) (representerSection f G W h)
      (representerSection_compatible f G W h Z q hcart hact)
  let s := hS.choose
  have hs : G.obj.map q.op s = representerSection f G W h := hS.choose_spec.1
  let η : X.smallEtaleTopology.yoneda.obj Z ⟶ G := X.smallEtaleTopology.yonedaEquiv.symm s
  have hη : IsIso η := by
    let 𝒰 : X.Cover.{u} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)) :=
      f.cover (P := show MorphismProperty Scheme.{u} from @Etale) inferInstance
    apply isIso_of_bijective_on_etaleCover 𝒰 η
    intro i T
    have hHom := etalePostcompose_hom_bijective_of_isPullback f W Z q hcart T
    apply (Function.Bijective.of_comp_iff _ hHom).mp
    have heq : (fun g : T ⟶ W =>
        η.hom.app (op ((etalePostcompose f).obj T)) ((etalePostcompose f).map g ≫ q)) =
        h.homEquiv := by
      funext g
      change G.obj.map ((etalePostcompose f).map g ≫ q).op s = h.homEquiv g
      rw [op_comp, G.obj.map_comp]
      change G.obj.map ((etalePostcompose f).map g).op (G.obj.map q.op s) = h.homEquiv g
      rw [hs]
      exact (h.homEquiv_eq g).symm
    change Function.Bijective (fun g : T ⟶ W =>
      η.hom.app (op ((etalePostcompose f).obj T)) ((etalePostcompose f).map g ≫ q))
    rw [heq]
    exact h.homEquiv.bijective
  exact Functor.representableByEquiv.symm
    ((sheafToPresheaf X.smallEtaleTopology (Type u)).mapIso (asIso η))

end EtaleCohomology
