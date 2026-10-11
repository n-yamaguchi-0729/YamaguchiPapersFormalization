/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Etale.ClosedNeighborhoodLift
import SchemeTheory.Etale.ClosedNeighborhoodEqualizer
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import EtaleCohomology.Sites.BaseChange
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Closed-subscheme neighborhoods and geometric points

The geometric neighborhood lifting theorem supplies an ambient étale
neighborhood and a map from its restriction to any prescribed pointed
étale neighborhood of the closed subscheme. We construct the corresponding
costructured arrow for base change on categories of elements.

The equalizing refinement theorem supplies the second part of the
initiality criterion for a functor with cofiltered domain. Thus the
costructured arrow categories are connected and the neighborhood functor
is initial, allowing stalks to be computed on ambient neighborhoods.
-/


noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits EtaleCohomology

namespace EtaleCohomology

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Z)

/-- Every pointed étale neighborhood of the closed subscheme receives a pointed
map from the restriction of an ambient étale neighborhood. -/
lemma closedNeighborhoodBaseChange_nonempty (N : (Scheme.pointSmallEtale s).fiber.Elements) :
    Nonempty (CostructuredArrow
      (Functor.Elements.precomp (etaleBaseChange i) (Scheme.pointSmallEtale s).fiber) N) := by
  obtain ⟨V, _, g, hg, h, _, hf, p, hp⟩ :=
    Etale.exists_neighborhood_lift_of_closedImmersion (P := Spec (.of Ω)) i N.obj.hom N.val.left
  have : Etale g := hg
  let A : X.Etale := MorphismProperty.Over.mk ⊤ g inferInstance
  let e : pullback g i ≅ pullback i g := pullbackSymmetry g i
  let q : Spec (.of Ω) ⟶ pullback g i := p ≫ e.inv
  have hs : q ≫ pullback.snd g i = s := by
    rw [Category.assoc, pullbackSymmetry_inv_comp_snd, ← hf, ← Category.assoc, hp]
    exact Over.w N.val
  let a : (etaleBaseChange i ⋙ (Scheme.pointSmallEtale s).fiber).Elements :=
    Functor.elementsMk _ A (Over.homMk q hs)
  let k : (etaleBaseChange i).obj A ⟶ N.obj :=
    MorphismProperty.Over.homMk (e.hom ≫ h) (by
      change (e.hom ≫ h) ≫ N.obj.hom = pullback.snd g i
      rw [Category.assoc, hf]
      exact pullbackSymmetry_hom_comp_fst g i)
  refine ⟨CostructuredArrow.mk (Y := a) ⟨k, ?_⟩⟩
  apply Over.OverMorphism.ext
  change (p ≫ e.inv) ≫ (e.hom ≫ h) = N.val.left
  rw [Category.assoc, Iso.inv_hom_id_assoc, hp]

/-- Base change along a closed immersion is initial on pointed étale neighborhoods. -/
theorem closedNeighborhoodBaseChange_initial :
    (Functor.Elements.precomp (etaleBaseChange i) (Scheme.pointSmallEtale s).fiber).Initial := by
  let : RepresentablyFlat (etaleBaseChange i) := flat_of_preservesFiniteLimits _
  apply Functor.initial_of_exists_of_isCofiltered
  · intro N
    obtain ⟨c⟩ := closedNeighborhoodBaseChange_nonempty i s N
    exact ⟨c.left, ⟨c.hom⟩⟩
  · intro N A a b
    let u : A.obj.left ⟶ X := A.obj.hom
    let p : Spec (.of Ω) ⟶ pullback u i := A.val.left
    let α : pullback u i ⟶ N.obj.left := a.hom.left
    let β : pullback u i ⟶ N.obj.left := b.hom.left
    have hab : α ≫ N.obj.hom = β ≫ N.obj.hom :=
      (MorphismProperty.Over.w a.hom).trans (MorphismProperty.Over.w b.hom).symm
    have ha : p ≫ α = N.val.left :=
      congrArg (fun r : Over.mk s ⟶ Over.mk N.obj.hom => r.left) a.map_val
    have hb : p ≫ β = N.val.left :=
      congrArg (fun r : Over.mk s ⟶ Over.mk N.obj.hom => r.left) b.map_val
    obtain ⟨V, g, hg, heq, q, hq⟩ :=
      Etale.exists_refinement_equalizing_of_closedImmersion (P := Spec (.of Ω))
        (pullback.fst u i) N.obj.hom α β hab p (ha.trans hb.symm)
    have : Etale g := hg
    let B : X.Etale := MorphismProperty.Over.mk ⊤ (g ≫ u) inferInstance
    let k : B ⟶ A.obj := MorphismProperty.Over.homMk g rfl
    let m : pullback (g ≫ u) i ⟶ pullback u i := ((etaleBaseChange i).map k).left
    have hm₁ : m ≫ pullback.fst u i = pullback.fst (g ≫ u) i ≫ g :=
      pullback.lift_fst _ _ _
    have hm₂ : m ≫ pullback.snd u i = pullback.snd (g ≫ u) i :=
      pullback.lift_snd _ _ _
    let E : pullback (pullback.fst u i) g ≅ pullback (g ≫ u) i :=
      pullbackSymmetry (pullback.fst u i) g ≪≫ pullbackRightPullbackFstIso u i g
    have hE₁ : E.hom ≫ pullback.fst (g ≫ u) i = pullback.snd (pullback.fst u i) g := by
      simp only [E, Iso.trans_hom, Category.assoc, pullbackRightPullbackFstIso_hom_fst,
        pullbackSymmetry_hom_comp_fst]
    have hE₂ : E.hom ≫ pullback.snd (g ≫ u) i =
        pullback.fst (pullback.fst u i) g ≫ pullback.snd u i := by
      simp only [E, Iso.trans_hom, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
        pullbackSymmetry_hom_comp_snd_assoc]
    have hEm : E.hom ≫ m = pullback.fst (pullback.fst u i) g := by
      apply pullback.hom_ext
      · rw [Category.assoc, hm₁, ← Category.assoc, hE₁]
        exact pullback.condition.symm
      · rw [Category.assoc, hm₂, hE₂]
    have hs : (q ≫ E.hom) ≫ pullback.snd (g ≫ u) i = s := by
      rw [Category.assoc, hE₂, ← Category.assoc, hq]
      exact Over.w A.val
    let c : (etaleBaseChange i ⋙ (Scheme.pointSmallEtale s).fiber).Elements :=
      Functor.elementsMk _ B (Over.homMk (q ≫ E.hom) hs)
    let t : c ⟶ A := ⟨k, by
      apply Over.OverMorphism.ext
      change (q ≫ E.hom) ≫ m = p
      rw [Category.assoc, hEm, hq]⟩
    refine ⟨c, t, ?_⟩
    apply Functor.Elements.Hom.ext
    apply MorphismProperty.Over.Hom.ext
    change m ≫ α = m ≫ β
    apply (cancel_epi E.hom).mp
    simp only [← Category.assoc, hEm]
    exact heq

end EtaleCohomology
