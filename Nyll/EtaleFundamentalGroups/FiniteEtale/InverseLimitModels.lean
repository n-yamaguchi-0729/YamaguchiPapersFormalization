/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The actual category of finite étale models over an inverse diagram

Objects and arrows are the native finite-étale comma category.  Base change
along a cone defines a functor on this category, and it inverts the
cartesian arrows used in the colimit construction.  No
descent statement is assumed in these constructions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale

universe u v w

variable {J : Type v} [Category.{w} J]

/-- A finite étale scheme over one actual member of the diagram. -/
def InverseLimitModel (F : J ⥤ Scheme.{u}) : Type (max v (u + 1)) :=
  MorphismProperty.Comma (𝟭 Scheme.{u}) F
    (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ ⊤

namespace InverseLimitModel

variable (F : J ⥤ Scheme.{u})

/-- The model category uses the native comma-category instance. -/
instance instCategory : Category.{max u w} (InverseLimitModel F) :=
  MorphismProperty.Comma.instCategory (𝟭 Scheme.{u}) F
    (@IsFiniteEtale : MorphismProperty Scheme.{u})
    (⊤ : MorphismProperty Scheme.{u}) (⊤ : MorphismProperty J)

/-- Cartesian transition arrows in the actual comma category. -/
def cartesian : MorphismProperty (InverseLimitModel F) :=
  fun {A B} f ↦ IsPullback f.left A.hom B.hom (F.map f.right)

instance cartesian_isMultiplicative : (cartesian F).IsMultiplicative where
  id_mem A := by
    change IsPullback (𝟙 A.left) A.hom A.hom (F.map (𝟙 A.right))
    rw [F.map_id]
    exact IsPullback.of_id_fst
  comp_mem {A B C} f g hf hg := by
    change IsPullback (f.left ≫ g.left) A.hom C.hom (F.map (f.right ≫ g.right))
    rw [F.map_comp]
    exact hf.paste_horiz hg

variable (s : Cone F)

/-- Pull an actual finite étale model back to the vertex of a cone. -/
def baseChangeObj (A : InverseLimitModel F) : FiniteEtale s.pt :=
  ⟨Over.mk (Limits.pullback.snd A.hom (s.π.app A.right)), by
    change IsFiniteEtale (Limits.pullback.snd A.hom (s.π.app A.right))
    exact MorphismProperty.of_isPullback
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback A.hom (s.π.app A.right)) A.prop⟩

private def conePullbackMap
    {A B X Y Z : Scheme.{u}} (f : A ⟶ Y) (g : B ⟶ Z)
    (p : X ⟶ Y) (q : X ⟶ Z) (a : A ⟶ B) (b : Y ⟶ Z)
    (ha : a ≫ g = f ≫ b) (hp : p ≫ b = q) :
    Limits.pullback f p ⟶ Limits.pullback g q :=
  Limits.pullback.lift (Limits.pullback.fst f p ≫ a) (Limits.pullback.snd f p) (by
    calc
      (Limits.pullback.fst f p ≫ a) ≫ g =
          Limits.pullback.fst f p ≫ (a ≫ g) := Category.assoc _ _ _
      _ = Limits.pullback.fst f p ≫ (f ≫ b) :=
        congrArg (fun t : A ⟶ Z ↦ Limits.pullback.fst f p ≫ t) ha
      _ = (Limits.pullback.fst f p ≫ f) ≫ b := (Category.assoc _ _ _).symm
      _ = (Limits.pullback.snd f p ≫ p) ≫ b :=
        congrArg (fun t : Limits.pullback f p ⟶ Y ↦ t ≫ b) Limits.pullback.condition
      _ = Limits.pullback.snd f p ≫ (p ≫ b) := Category.assoc _ _ _
      _ = Limits.pullback.snd f p ≫ q :=
        congrArg (fun t : X ⟶ Z ↦ Limits.pullback.snd f p ≫ t) hp)

/-- The morphism on actual pullbacks induced by a model arrow. -/
def baseChangeHom {A B : InverseLimitModel F} (f : A ⟶ B) :
    baseChangeObj F s A ⟶ baseChangeObj F s B :=
  MorphismProperty.Over.homMk
    (conePullbackMap A.hom B.hom (s.π.app A.right) (s.π.app B.right)
      f.left (F.map f.right) f.w (s.w f.right))
    (Limits.pullback.lift_snd _ _ _)

/-- The base-change morphism retains the original arrow on the cover. -/
theorem baseChangeHom_fst {A B : InverseLimitModel F} (f : A ⟶ B) :
    (baseChangeHom F s f).left ≫ Limits.pullback.fst B.hom (s.π.app B.right) =
      Limits.pullback.fst A.hom (s.π.app A.right) ≫ f.left :=
  Limits.pullback.lift_fst _ _ _

/-- The base-change morphism is over the cone vertex. -/
theorem baseChangeHom_snd {A B : InverseLimitModel F} (f : A ⟶ B) :
    (baseChangeHom F s f).left ≫ Limits.pullback.snd B.hom (s.π.app B.right) =
      Limits.pullback.snd A.hom (s.π.app A.right) :=
  Limits.pullback.lift_snd _ _ _

/-- Base change along a cone is a genuine functor on the category of models. -/
def baseChange : InverseLimitModel F ⥤ FiniteEtale s.pt where
  obj := baseChangeObj F s
  map := baseChangeHom F s
  map_id A := by
    apply MorphismProperty.Over.Hom.ext
    apply Limits.pullback.hom_ext
    · change (baseChangeHom F s (𝟙 A)).left ≫
        Limits.pullback.fst A.hom (s.π.app A.right) =
        𝟙 _ ≫ Limits.pullback.fst A.hom (s.π.app A.right)
      rw [baseChangeHom_fst, Category.id_comp]
      exact Category.comp_id _
    · change (baseChangeHom F s (𝟙 A)).left ≫
        Limits.pullback.snd A.hom (s.π.app A.right) =
        𝟙 _ ≫ Limits.pullback.snd A.hom (s.π.app A.right)
      rw [baseChangeHom_snd, Category.id_comp]
  map_comp {A B C} f g := by
    let XA : Scheme := A.left
    let XB : Scheme := B.left
    let XC : Scheme := C.left
    let fA : XA ⟶ F.obj A.right := A.hom
    let fB : XB ⟶ F.obj B.right := B.hom
    let fC : XC ⟶ F.obj C.right := C.hom
    let PA : Scheme := Limits.pullback fA (s.π.app A.right)
    let PB : Scheme := Limits.pullback fB (s.π.app B.right)
    let PC : Scheme := Limits.pullback fC (s.π.app C.right)
    let f₀ : XA ⟶ XB := f.left
    let g₀ : XB ⟶ XC := g.left
    let u : PA ⟶ PB := (baseChangeHom F s f).left
    let v : PB ⟶ PC := (baseChangeHom F s g).left
    let uv : PA ⟶ PC := (baseChangeHom F s (f ≫ g)).left
    let pA : PA ⟶ XA := Limits.pullback.fst fA (s.π.app A.right)
    let pB : PB ⟶ XB := Limits.pullback.fst fB (s.π.app B.right)
    let pC : PC ⟶ XC := Limits.pullback.fst fC (s.π.app C.right)
    let qA : PA ⟶ s.pt := Limits.pullback.snd fA (s.π.app A.right)
    let qB : PB ⟶ s.pt := Limits.pullback.snd fB (s.π.app B.right)
    let qC : PC ⟶ s.pt := Limits.pullback.snd fC (s.π.app C.right)
    have hu : u ≫ pB = pA ≫ f₀ := baseChangeHom_fst F s f
    have hv : v ≫ pC = pB ≫ g₀ := baseChangeHom_fst F s g
    have huv : uv ≫ pC = pA ≫ (f₀ ≫ g₀) := baseChangeHom_fst F s (f ≫ g)
    have huS : u ≫ qB = qA := baseChangeHom_snd F s f
    have hvS : v ≫ qC = qB := baseChangeHom_snd F s g
    have huvS : uv ≫ qC = qA := baseChangeHom_snd F s (f ≫ g)
    apply MorphismProperty.Over.Hom.ext
    change uv = u ≫ v
    apply Limits.pullback.hom_ext
    · change uv ≫ pC = (u ≫ v) ≫ pC
      calc
        uv ≫ pC = pA ≫ (f₀ ≫ g₀) := huv
        _ = (pA ≫ f₀) ≫ g₀ := (Category.assoc pA f₀ g₀).symm
        _ = (u ≫ pB) ≫ g₀ := congrArg (fun t : PA ⟶ XB ↦ t ≫ g₀) hu.symm
        _ = u ≫ (pB ≫ g₀) := Category.assoc u pB g₀
        _ = u ≫ (v ≫ pC) := congrArg (fun t : PB ⟶ XC ↦ u ≫ t) hv.symm
        _ = (u ≫ v) ≫ pC := (Category.assoc u v pC).symm
    · change uv ≫ qC = (u ≫ v) ≫ qC
      calc
        uv ≫ qC = qA := huvS
        _ = u ≫ qB := huS.symm
        _ = u ≫ (v ≫ qC) := congrArg (fun t : PB ⟶ s.pt ↦ u ≫ t) hvS.symm
        _ = (u ≫ v) ≫ qC := (Category.assoc u v qC).symm

/-- Cartesian arrows become isomorphisms after base change along the cone. -/
theorem baseChange_inverts_cartesian : (cartesian F).IsInvertedBy (baseChange F s) := by
  intro A B f hf
  have hp : IsPullback
      (Limits.pullback.fst A.hom (s.π.app A.right) ≫ f.left)
      (Limits.pullback.snd A.hom (s.π.app A.right)) B.hom (s.π.app B.right) := by
    have h := (IsPullback.of_hasPullback A.hom (s.π.app A.right)).paste_horiz hf
    rw [s.w f.right] at h
    exact h
  let e : baseChangeObj F s A ≅ baseChangeObj F s B :=
    MorphismProperty.Over.isoMk hp.isoPullback hp.isoPullback_hom_snd
  have he : e.hom = baseChangeHom F s f := by
    apply MorphismProperty.Over.Hom.ext
    apply Limits.pullback.hom_ext
    · exact hp.isoPullback_hom_fst.trans (baseChangeHom_fst F s f).symm
    · exact hp.isoPullback_hom_snd.trans (baseChangeHom_snd F s f).symm
  change IsIso (baseChangeHom F s f)
  rw [← he]
  infer_instance

/-- The actual comparison functor out of the localization of models. -/
def localizedBaseChange : (cartesian F).Localization ⥤ FiniteEtale s.pt :=
  Localization.Construction.lift (baseChange F s) (baseChange_inverts_cartesian F s)

/-- Restricting the localized comparison to the model category recovers the
actual base-change functor. -/
theorem q_comp_localizedBaseChange :
    (cartesian F).Q ⋙ localizedBaseChange F s = baseChange F s :=
  Localization.Construction.fac (baseChange F s) (baseChange_inverts_cartesian F s)

end InverseLimitModel

end AlgebraicGeometry.FiniteEtale
