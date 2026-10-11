/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.PullbackComposition
import EtaleCohomology.Sites.PushforwardStalkComparison
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Composition of actual direct-image stalk components

The concrete maps on representing neighborhoods commute with the chosen
pullback-pasting isomorphism. Passing to stalks retains this equation.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {X Y Z : Scheme.{u}} (p : Z ⟶ Y) (q : Y ⟶ X)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (t : Spec (CommRingCat.of Ω) ⟶ X)
  (s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t})
  (r : {r : Spec (CommRingCat.of Ω) ⟶ Z // r ≫ p = s.val})

/-- Geometric lifts into successive base changes agree with the lift into
the composite base change under the actual pasting isomorphism. -/
lemma etalePushforwardGeometricLift_comp (U : X.Etale)
    (a : (Scheme.pointSmallEtale t).fiber.obj U) :
    (Scheme.pointSmallEtale r.val).fiber.map
        ((MorphismProperty.Over.pullbackComp
          (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) p q).hom.app U)
        (etalePushforwardGeometricLift (p ≫ q) t
          ⟨r.val, by rw [← Category.assoc, r.property, s.property]⟩ U a) =
      etalePushforwardGeometricLift p s.val r ((etaleBaseChange q).obj U)
        (etalePushforwardGeometricLift q t s U a) := by
  let B : Y.Etale := (etaleBaseChange q).obj U
  let C : Z.Etale := (etaleBaseChange p).obj B
  let D : Z.Etale := (etaleBaseChange (p ≫ q)).obj U
  let e : D ⟶ C := (MorphismProperty.Over.pullbackComp
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) p q).hom.app U
  let b : Spec (CommRingCat.of Ω) ⟶ B.left :=
    (etalePushforwardGeometricLift q t s U a).left
  let c : Spec (CommRingCat.of Ω) ⟶ C.left :=
    (etalePushforwardGeometricLift p s.val r B
      (etalePushforwardGeometricLift q t s U a)).left
  let d : Spec (CommRingCat.of Ω) ⟶ D.left :=
    (etalePushforwardGeometricLift (p ≫ q) t
      ⟨r.val, by rw [← Category.assoc, r.property, s.property]⟩ U a).left
  let π : C.left ⟶ B.left := pullback.fst B.hom p
  let ρ : B.left ⟶ U.left := pullback.fst U.hom q
  let δ : D.left ⟶ U.left := pullback.fst U.hom (p ≫ q)
  have he : e.left ≫ π ≫ ρ = δ :=
    MorphismProperty.Over.pullbackComp_left_fst_fst
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) p q U
  have hd : d ≫ δ = a.left := pullback.lift_fst _ _ _
  have hb : b ≫ ρ = a.left := pullback.lift_fst _ _ _
  have hc : c ≫ π = b := pullback.lift_fst _ _ _
  have hcZ : c ≫ C.hom = r.val := pullback.lift_snd _ _ _
  have hdZ : d ≫ D.hom = r.val := pullback.lift_snd _ _ _
  have hπ : π ≫ B.hom = C.hom ≫ p := pullback.condition
  have heZ : e.left ≫ C.hom = D.hom := e.w
  have hz : (d ≫ e.left) ≫ C.hom = c ≫ C.hom :=
    (Category.assoc d e.left C.hom).trans
      ((congrArg (fun k : D.left ⟶ Z => d ≫ k) heZ).trans (hdZ.trans hcZ.symm))
  have hw (k : Spec (CommRingCat.of Ω) ⟶ C.left) :
      (k ≫ π) ≫ B.hom = (k ≫ C.hom) ≫ p :=
    (Category.assoc k π B.hom).trans
      ((congrArg (fun z : C.left ⟶ Y => k ≫ z) hπ).trans (Category.assoc k C.hom p).symm)
  apply Over.OverMorphism.ext
  change d ≫ e.left = c
  apply pullback.hom_ext
  · change (d ≫ e.left) ≫ π = c ≫ π
    apply pullback.hom_ext
    · change ((d ≫ e.left) ≫ π) ≫ ρ = (c ≫ π) ≫ ρ
      rw [Category.assoc, Category.assoc, he, hd, hc, hb]
    · change ((d ≫ e.left) ≫ π) ≫ B.hom = (c ≫ π) ≫ B.hom
      exact (hw (d ≫ e.left)).trans
        ((congrArg (fun k : Spec (CommRingCat.of Ω) ⟶ Z => k ≫ p) hz).trans (hw c).symm)
  · change (d ≫ e.left) ≫ C.hom = c ≫ C.hom
    exact hz

variable (Λ : Type u) [CommRing Λ]

/-- Direct-image geometric stalk components compose through the chosen
comparison for the composite scheme morphism. -/
theorem etalePushforwardStalkComponent_comp
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (Scheme.pointSmallEtale t).sheafFiber.map
        ((etalePushforwardCompIso p q Λ).hom.app F) ≫
      etalePushforwardStalkComponent (p ≫ q) t
        ⟨r.val, by rw [← Category.assoc, r.property, s.property]⟩ F =
      etalePushforwardStalkComponent q t s ((etalePushforward p Λ).obj F) ≫
        etalePushforwardStalkComponent p s.val r F := by
  let G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) := (etalePushforward p Λ).obj F
  let P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ := ((etalePushforward q Λ).obj G).obj
  let Q : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ := ((etalePushforward (p ≫ q) Λ).obj F).obj
  let η : P ⟶ Q := ((etalePushforwardCompIso p q Λ).hom.app F).hom
  let k : (Scheme.pointSmallEtale t).presheafFiber.obj Q ⟶
      (Scheme.pointSmallEtale r.val).presheafFiber.obj F.obj :=
    etalePushforwardStalkComponent (p ≫ q) t
      ⟨r.val, by rw [← Category.assoc, r.property, s.property]⟩ F
  let cq : (Scheme.pointSmallEtale t).presheafFiber.obj P ⟶
      (Scheme.pointSmallEtale s.val).presheafFiber.obj G.obj :=
    etalePushforwardStalkComponent q t s G
  let cp : (Scheme.pointSmallEtale s.val).presheafFiber.obj G.obj ⟶
      (Scheme.pointSmallEtale r.val).presheafFiber.obj F.obj :=
    etalePushforwardStalkComponent p s.val r F
  change (Scheme.pointSmallEtale t).presheafFiber.map η ≫ k = cq ≫ cp
  apply (Scheme.pointSmallEtale t).presheafFiber_hom_ext
  intro U a
  let B : Y.Etale := (etaleBaseChange q).obj U
  let C : Z.Etale := (etaleBaseChange p).obj B
  let D : Z.Etale := (etaleBaseChange (p ≫ q)).obj U
  let e : D ⟶ C := (MorphismProperty.Over.pullbackComp
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) p q).hom.app U
  let b := etalePushforwardGeometricLift q t s U a
  let c := etalePushforwardGeometricLift p s.val r B b
  let d := etalePushforwardGeometricLift (p ≫ q) t
    ⟨r.val, by rw [← Category.assoc, r.property, s.property]⟩ U a
  have hη : η.app (op U) = F.obj.map e.op := by
    change 𝟙 _ ≫ F.obj.map e.op = F.obj.map e.op
    exact Category.id_comp _
  have hq : (Scheme.pointSmallEtale t).toPresheafFiber U a P ≫ cq =
      (Scheme.pointSmallEtale s.val).toPresheafFiber B b G.obj :=
    toPresheafFiber_etalePushforwardStalkComponent q t s G U a
  have hp : (Scheme.pointSmallEtale s.val).toPresheafFiber B b G.obj ≫ cp =
      (Scheme.pointSmallEtale r.val).toPresheafFiber C c F.obj :=
    toPresheafFiber_etalePushforwardStalkComponent p s.val r F B b
  have hk : (Scheme.pointSmallEtale t).toPresheafFiber U a Q ≫ k =
      (Scheme.pointSmallEtale r.val).toPresheafFiber D d F.obj :=
    toPresheafFiber_etalePushforwardStalkComponent (p ≫ q) t
      ⟨r.val, by rw [← Category.assoc, r.property, s.property]⟩ F U a
  rw [← Category.assoc, (Scheme.pointSmallEtale t).toPresheafFiber_naturality,
    Category.assoc, hk, ← Category.assoc _ cq, hq]
  refine Eq.trans ?_ hp.symm
  refine (congrArg (fun h : F.obj.obj (op C) ⟶ F.obj.obj (op D) =>
    h ≫ (Scheme.pointSmallEtale r.val).toPresheafFiber D d F.obj) hη).trans ?_
  refine ((Scheme.pointSmallEtale r.val).toPresheafFiber_w e d F.obj).trans ?_
  exact congrArg (fun z => (Scheme.pointSmallEtale r.val).toPresheafFiber C z F.obj)
    (etalePushforwardGeometricLift_comp p q t s r U a)

end EtaleCohomology
