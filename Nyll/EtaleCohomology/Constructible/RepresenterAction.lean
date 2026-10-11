/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.EtaleRestriction
import Nyll.SchemeTheory.Descent.AffineCocycle
import Nyll.SchemeTheory.Descent.ActionOverlap
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Yoneda

/-!
# Descent actions supplied by a local representer

The universal section of a representer on an étale cover constructs its
descent action. The unit and action laws follow from the actual naturality
and uniqueness in the representing equivalence.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
variable (G : Sheaf X.smallEtaleTopology (Type u)) (W : Y.Etale)
variable (h : ((etalePostcompose f).op ⋙ G.obj).RepresentableBy W)

/-- The universal section of the original sheaf on the local representing scheme. -/
def representerSection : G.obj.obj (op ((etalePostcompose f).obj W)) :=
  h.homEquiv (𝟙 W)

/-- Equality of maps to a representer is detected by its universal section. -/
lemma representerSection_hom_ext {T : Y.Etale} (a b : T ⟶ W)
    (hab : G.obj.map ((etalePostcompose f).map a).op (representerSection f G W h) =
      G.obj.map ((etalePostcompose f).map b).op (representerSection f G W h)) : a = b := by
  apply h.homEquiv.injective
  exact (h.homEquiv_eq a).trans (hab.trans (h.homEquiv_eq b).symm)

/-- The pullback on which the descent action is defined, as an object over the cover. -/
def representerActionDomain : Y.Etale :=
  MorphismProperty.Over.mk ⊤ (pullback.fst f (W.hom ≫ f)) inferInstance

/-- The second overlap projection, viewed on the original small étale site. -/
def representerActionSecond :
    (etalePostcompose f).obj (representerActionDomain f W) ⟶
      (etalePostcompose f).obj W :=
  MorphismProperty.Over.homMk (pullback.snd f (W.hom ≫ f))
    (by exact pullback.condition.symm) trivial

/-- The original sheaf's universal section determines a map from the overlap. -/
def representerActionHom : representerActionDomain f W ⟶ W :=
  h.homEquiv.symm (G.obj.map (representerActionSecond f W).op
    (representerSection f G W h))

/-- The geometric descent action obtained from local representability. -/
def representerAction : pullback f (W.hom ≫ f) ⟶ W.left :=
  (representerActionHom f G W h).left

lemma representerAction_over : representerAction f G W h ≫ W.hom =
    pullback.fst f (W.hom ≫ f) :=
  MorphismProperty.Over.w (representerActionHom f G W h)

lemma representerAction_base : representerAction f G W h ≫ (W.hom ≫ f) =
    pullback.fst f (W.hom ≫ f) ≫ f := by
  rw [← Category.assoc, representerAction_over]

/-- The universal section is invariant under the constructed descent action. -/
lemma representerAction_section :
    G.obj.map ((etalePostcompose f).map (representerActionHom f G W h)).op
        (representerSection f G W h) =
      G.obj.map (representerActionSecond f W).op (representerSection f G W h) := by
  exact (h.homEquiv_eq (representerActionHom f G W h)).symm.trans
    (h.homEquiv.apply_symm_apply _)

private lemma representerActionHom_naturality {T : Y.Etale}
    (a : T ⟶ representerActionDomain f W) :
    h.homEquiv (a ≫ representerActionHom f G W h) =
      G.obj.map ((etalePostcompose f).map a ≫ representerActionSecond f W).op
        (representerSection f G W h) := by
  rw [h.homEquiv_comp]
  change G.obj.map ((etalePostcompose f).map a).op
      (h.homEquiv (h.homEquiv.symm _)) = _
  exact (congrArg (fun x => G.obj.map ((etalePostcompose f).map a).op x)
    (h.homEquiv.apply_symm_apply _)).trans
      (congrArg (fun k => k (representerSection f G W h))
        (G.obj.map_comp (representerActionSecond f W).op
          ((etalePostcompose f).map a).op)).symm

/-- Acting along the diagonal recovers the original point of the representer. -/
lemma representerAction_unit :
    pullback.lift (f := f) (g := W.hom ≫ f) W.hom (𝟙 W.left)
        (Category.id_comp (W.hom ≫ f)).symm ≫
      representerAction f G W h = 𝟙 W.left := by
  let d : W ⟶ representerActionDomain f W :=
    MorphismProperty.Over.homMk
      (pullback.lift (f := f) (g := W.hom ≫ f) W.hom (𝟙 W.left)
        (Category.id_comp (W.hom ≫ f)).symm)
      (pullback.lift_fst _ _ _) trivial
  have hd : (etalePostcompose f).map d ≫ representerActionSecond f W =
      𝟙 ((etalePostcompose f).obj W) := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_snd _ _ _
  have he : d ≫ representerActionHom f G W h = 𝟙 W := by
    apply h.homEquiv.injective
    rw [representerActionHom_naturality, hd, op_id, G.obj.map_id]
    rfl
  exact congrArg (fun a : W ⟶ W => a.left) he

/-- The descent action satisfies the genuine triple-pullback action law. -/
lemma representerAction_assoc :
    pullbackActionStep f (W.hom ≫ f) (representerAction f G W h)
        (representerAction_base f G W h) ≫ representerAction f G W h =
      pullbackSkipMiddle f (W.hom ≫ f) ≫ representerAction f G W h := by
  let P := representerActionDomain f W
  let T : Y.Etale := MorphismProperty.Over.mk ⊤
    (pullback.fst f (pullback.fst f (W.hom ≫ f) ≫ f)) inferInstance
  let k : T ⟶ P := MorphismProperty.Over.homMk
    (pullbackActionStep f (W.hom ≫ f) (representerAction f G W h)
      (representerAction_base f G W h)) (pullback.lift_fst _ _ _) trivial
  let l : T ⟶ P := MorphismProperty.Over.homMk
    (pullbackSkipMiddle f (W.hom ≫ f)) (pullback.lift_fst _ _ _) trivial
  let b : (etalePostcompose f).obj T ⟶ (etalePostcompose f).obj P :=
    MorphismProperty.Over.homMk
      (pullback.snd f (pullback.fst f (W.hom ≫ f) ≫ f))
      (pullback.condition.symm) trivial
  have hk : (etalePostcompose f).map k ≫ representerActionSecond f W =
      b ≫ (etalePostcompose f).map (representerActionHom f G W h) := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_snd _ _ _
  have hl : (etalePostcompose f).map l ≫ representerActionSecond f W =
      b ≫ representerActionSecond f W := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_snd _ _ _
  have he : k ≫ representerActionHom f G W h =
      l ≫ representerActionHom f G W h := by
    apply h.homEquiv.injective
    rw [representerActionHom_naturality, representerActionHom_naturality, hk, hl,
      op_comp, op_comp, G.obj.map_comp, G.obj.map_comp]
    change G.obj.map b.op
        (G.obj.map ((etalePostcompose f).map (representerActionHom f G W h)).op
          (representerSection f G W h)) =
      G.obj.map b.op (G.obj.map (representerActionSecond f W).op (representerSection f G W h))
    exact congrArg (fun s => G.obj.map b.op s) (representerAction_section f G W h)
  exact congrArg (fun a : T ⟶ W => a.left) he

/-- The two overlap pullbacks of a local representer are canonically isomorphic.
All the action laws are supplied by the original sheaf's universal section. -/
def representerOverlapIso : pullback f (W.hom ≫ f) ≅ pullback (W.hom ≫ f) f :=
  pullbackActionOverlapIso f W.hom (representerAction f G W h)
    (representerAction_over f G W h) (representerAction_unit f G W h)
    (representerAction_assoc f G W h)

/-- The overlap isomorphism induces exactly the constructed descent action. -/
lemma representerOverlapIso_hom_fst :
    (representerOverlapIso f G W h).hom ≫ pullback.fst (W.hom ≫ f) f =
      representerAction f G W h :=
  pullbackActionOverlapIso_hom_fst f W.hom (representerAction f G W h)
    (representerAction_over f G W h) (representerAction_unit f G W h)
    (representerAction_assoc f G W h)

end EtaleCohomology
