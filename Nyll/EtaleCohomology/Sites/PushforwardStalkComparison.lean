/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.BaseChange
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Continuous

/-!
# The actual stalk comparison for étale direct image

An ambient pointed étale neighborhood pulls back to a pointed neighborhood
at every lift of the geometric point. Passing to the defining stalk colimits
constructs the canonical direct-image stalk map to the product of the lifted
stalks. The construction applies to every scheme morphism and is natural in
the sheaf. Finiteness and algebraic closedness enter only in the later proof
that this comparison is an isomorphism for finite morphisms.
-/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (q : Y ⟶ X)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (t : Spec (CommRingCat.of Ω) ⟶ X)
  (s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t})

/-- The actual lift into the scheme-theoretic base change of a pointed
étale neighborhood. -/
def etalePushforwardGeometricLift (U : X.Etale)
    (a : (Scheme.pointSmallEtale t).fiber.obj U) :
    (Scheme.pointSmallEtale s.val).fiber.obj ((etaleBaseChange q).obj U) := by
  let f : U.left ⟶ X := U.hom
  let a₀ : Spec (CommRingCat.of Ω) ⟶ U.left := a.left
  have ha : a₀ ≫ f = t := a.w
  have h : a₀ ≫ f = s.val ≫ q := ha.trans s.property.symm
  exact Over.homMk (pullback.lift a₀ s.val h) (pullback.lift_snd _ _ _)

/-- The geometric lifts commute with a morphism of ambient neighborhoods. -/
lemma etalePushforwardGeometricLift_naturality {U V : X.Etale} (g : U ⟶ V)
    (a : (Scheme.pointSmallEtale t).fiber.obj U) :
    (Scheme.pointSmallEtale s.val).fiber.map ((etaleBaseChange q).map g)
        (etalePushforwardGeometricLift q t s U a) =
      etalePushforwardGeometricLift q t s V ((Scheme.pointSmallEtale t).fiber.map g a) := by
  let U₀ : Scheme.{u} := U.left
  let V₀ : Scheme.{u} := V.left
  let f : U₀ ⟶ X := U.hom
  let h : V₀ ⟶ X := V.hom
  let g₀ : U₀ ⟶ V₀ := g.left
  let a₀ : Spec (CommRingCat.of Ω) ⟶ U₀ := a.left
  let s₀ : Spec (CommRingCat.of Ω) ⟶ Y := s.val
  let x : Spec (CommRingCat.of Ω) ⟶ pullback f q :=
    (etalePushforwardGeometricLift q t s U a).left
  let y : Spec (CommRingCat.of Ω) ⟶ pullback h q :=
    (etalePushforwardGeometricLift q t s V ((Scheme.pointSmallEtale t).fiber.map g a)).left
  let m : pullback f q ⟶ pullback h q := ((etaleBaseChange q).map g).left
  have hx₁ : x ≫ pullback.fst f q = a₀ := pullback.lift_fst _ _ _
  have hx₂ : x ≫ pullback.snd f q = s₀ := pullback.lift_snd _ _ _
  have hy₁ : y ≫ pullback.fst h q = a₀ ≫ g₀ := pullback.lift_fst _ _ _
  have hy₂ : y ≫ pullback.snd h q = s₀ := pullback.lift_snd _ _ _
  have hm₁ : m ≫ pullback.fst h q = pullback.fst f q ≫ g₀ := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd h q = pullback.snd f q := pullback.lift_snd _ _ _
  apply Over.OverMorphism.ext
  change x ≫ m = y
  apply pullback.hom_ext
  · rw [Category.assoc, hm₁, ← Category.assoc, hx₁, hy₁]
  · rw [Category.assoc, hm₂, hx₂, hy₂]

variable {A : Type v} [Category.{w} A] [HasColimitsOfSize.{u, u} A]
  (F : Sheaf Y.smallEtaleTopology A)

/-- Restricting a direct-image germ to a chosen geometric lift. -/
def etalePushforwardStalkComponent :
    (Scheme.pointSmallEtale t).sheafFiber.obj
        (((etaleBaseChange q).sheafPushforwardContinuous A
          X.smallEtaleTopology Y.smallEtaleTopology).obj F) ⟶
      (Scheme.pointSmallEtale s.val).sheafFiber.obj F :=
  (Scheme.pointSmallEtale t).presheafFiberDesc
    (fun U a => (Scheme.pointSmallEtale s.val).toPresheafFiber
      ((etaleBaseChange q).obj U) (etalePushforwardGeometricLift q t s U a) F.obj)
    (by
      intro U V g a
      change F.obj.map ((etaleBaseChange q).map g).op ≫
          (Scheme.pointSmallEtale s.val).toPresheafFiber
            ((etaleBaseChange q).obj U) (etalePushforwardGeometricLift q t s U a) F.obj = _
      rw [(Scheme.pointSmallEtale s.val).toPresheafFiber_w,
        etalePushforwardGeometricLift_naturality])

/-- The component comparison sends a representing section to its actual germ
in the pullback neighborhood. -/
lemma toPresheafFiber_etalePushforwardStalkComponent (U : X.Etale)
    (a : (Scheme.pointSmallEtale t).fiber.obj U) :
    (Scheme.pointSmallEtale t).toPresheafFiber U a
        (((etaleBaseChange q).sheafPushforwardContinuous A
          X.smallEtaleTopology Y.smallEtaleTopology).obj F).obj ≫
        etalePushforwardStalkComponent q t s F =
      (Scheme.pointSmallEtale s.val).toPresheafFiber
        ((etaleBaseChange q).obj U) (etalePushforwardGeometricLift q t s U a) F.obj :=
  (Scheme.pointSmallEtale t).toPresheafFiber_presheafFiberDesc _ _ U a

variable {F} {G : Sheaf Y.smallEtaleTopology A}

/-- The component comparison is natural in the actual sheaf. -/
lemma etalePushforwardStalkComponent_naturality (η : F ⟶ G) :
    (Scheme.pointSmallEtale t).sheafFiber.map
        (((etaleBaseChange q).sheafPushforwardContinuous A
          X.smallEtaleTopology Y.smallEtaleTopology).map η) ≫
        etalePushforwardStalkComponent q t s G =
      etalePushforwardStalkComponent q t s F ≫
        (Scheme.pointSmallEtale s.val).sheafFiber.map η := by
  let P : X.Etaleᵒᵖ ⥤ A :=
    (((etaleBaseChange q).sheafPushforwardContinuous A
      X.smallEtaleTopology Y.smallEtaleTopology).obj F).obj
  let Q : X.Etaleᵒᵖ ⥤ A :=
    (((etaleBaseChange q).sheafPushforwardContinuous A
      X.smallEtaleTopology Y.smallEtaleTopology).obj G).obj
  let ηP : P ⟶ Q :=
    (((etaleBaseChange q).sheafPushforwardContinuous A
      X.smallEtaleTopology Y.smallEtaleTopology).map η).hom
  let f : (Scheme.pointSmallEtale t).presheafFiber.obj P ⟶
      (Scheme.pointSmallEtale s.val).presheafFiber.obj F.obj :=
    etalePushforwardStalkComponent q t s F
  let g : (Scheme.pointSmallEtale t).presheafFiber.obj Q ⟶
      (Scheme.pointSmallEtale s.val).presheafFiber.obj G.obj :=
    etalePushforwardStalkComponent q t s G
  change (Scheme.pointSmallEtale t).presheafFiber.map ηP ≫ g =
    f ≫ (Scheme.pointSmallEtale s.val).presheafFiber.map η.hom
  apply (Scheme.pointSmallEtale t).presheafFiber_hom_ext
  intro U a
  have hf : (Scheme.pointSmallEtale t).toPresheafFiber U a P ≫ f =
      (Scheme.pointSmallEtale s.val).toPresheafFiber
        ((etaleBaseChange q).obj U) (etalePushforwardGeometricLift q t s U a) F.obj :=
    toPresheafFiber_etalePushforwardStalkComponent q t s F U a
  have hg : (Scheme.pointSmallEtale t).toPresheafFiber U a Q ≫ g =
      (Scheme.pointSmallEtale s.val).toPresheafFiber
        ((etaleBaseChange q).obj U) (etalePushforwardGeometricLift q t s U a) G.obj :=
    toPresheafFiber_etalePushforwardStalkComponent q t s G U a
  rw [← Category.assoc, (Scheme.pointSmallEtale t).toPresheafFiber_naturality,
    Category.assoc, hg, ← Category.assoc, hf]
  exact ((Scheme.pointSmallEtale s.val).toPresheafFiber_naturality η.hom
    ((etaleBaseChange q).obj U) (etalePushforwardGeometricLift q t s U a)).symm

variable [HasProducts.{u} A] (F)

/-- The canonical map from a direct-image geometric stalk to the product
of the stalks at all geometric lifts with the same field. -/
def etalePushforwardStalkComparison :
    (Scheme.pointSmallEtale t).sheafFiber.obj
        (((etaleBaseChange q).sheafPushforwardContinuous A
          X.smallEtaleTopology Y.smallEtaleTopology).obj F) ⟶
      ∏ᶜ fun s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t} =>
        (Scheme.pointSmallEtale s.val).sheafFiber.obj F :=
  Pi.lift (fun s => etalePushforwardStalkComponent q t s F)

/-- Every product projection is the corresponding actual germ comparison. -/
lemma etalePushforwardStalkComparison_π :
    etalePushforwardStalkComparison q t F ≫
        Pi.π (fun s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t} =>
          (Scheme.pointSmallEtale s.val).sheafFiber.obj F) s =
      etalePushforwardStalkComponent q t s F :=
  Pi.lift_comp_π _ _

end EtaleCohomology
