/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.PullbackSections
import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
import Nyll.EtaleCohomology.Sites.PushforwardStalkComparison

/-!
# Global sections of actual étale direct image

The base change of the identity object is canonically the identity object.
Restriction through this isomorphism identifies global sections, and its
geometric germs are the concrete direct-image stalk components.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (q : Y ⟶ X)

private def baseChangeIdentityIso :
    (Scheme.Etale.mk (𝟙 Y) : Y.Etale) ≅ (etaleBaseChange q).obj (Scheme.Etale.mk (𝟙 X)) := by
  let B : Y.Etale := (etaleBaseChange q).obj (Scheme.Etale.mk (𝟙 X))
  let j : (Scheme.Etale.mk (𝟙 Y) : Y.Etale) ⟶ B :=
    etaleBaseChangeLift q q ((Category.comp_id q).trans (Category.id_comp q).symm)
  let k : B ⟶ Scheme.Etale.mk (𝟙 Y) := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    B.hom (Category.comp_id B.hom)
  have hj : j.left ≫ B.hom = 𝟙 Y := j.w
  have : IsIso B.hom := inferInstanceAs (IsIso (pullback.snd (𝟙 X) q))
  refine ⟨j, k, ?_, ?_⟩
  · apply MorphismProperty.Over.Hom.ext
    exact hj
  · apply MorphismProperty.Over.Hom.ext
    change B.hom ≫ j.left = 𝟙 B.left
    apply (cancel_mono B.hom).mp
    exact (Category.assoc B.hom j.left B.hom).trans
      ((congrArg (fun z : Y ⟶ Y => B.hom ≫ z) hj).trans
        ((Category.comp_id B.hom).trans (Category.id_comp B.hom).symm))

variable (Λ : Type u) [CommRing Λ]

/-- Global sections of actual direct image are the original global sections. -/
def etalePushforwardGlobalSectionsIso
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((etalePushforward q Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 X))) ≅
      F.obj.obj (op (Scheme.Etale.mk (𝟙 Y))) :=
  F.obj.mapIso (baseChangeIdentityIso q).op

/-- The forward comparison is restriction through the actual base-change lift. -/
lemma etalePushforwardGlobalSectionsIso_hom
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (etalePushforwardGlobalSectionsIso q Λ F).hom =
      F.obj.map (etaleBaseChangeLift q q
        ((Category.comp_id q).trans (Category.id_comp q).symm)).op := rfl

/-- Evaluation of the unit followed by the direct-image section comparison
is the original global inverse-image map. -/
lemma etalePullbackGlobalSectionsMap_eq_unit
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((etalePullbackPushforwardAdjunction q Λ).unit.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 X))) ≫
      (etalePushforwardGlobalSectionsIso q Λ ((etalePullback q Λ).obj F)).hom =
        etalePullbackGlobalSectionsMap q Λ F := rfl

/-- A global direct-image germ restricts to the germ of the corresponding
original global section at each geometric lift. -/
theorem etalePushforwardGlobalSectionsIso_germ
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ X)
    (s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t})
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etaleGlobalSectionsGerm t Λ ((etalePushforward q Λ).obj F) ≫
        etalePushforwardStalkComponent q t s F =
      (etalePushforwardGlobalSectionsIso q Λ F).hom ≫
        etaleGlobalSectionsGerm s.val Λ F := by
  let X₀ : X.Etale := Scheme.Etale.mk (𝟙 X)
  let Y₀ : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  let B : Y.Etale := (etaleBaseChange q).obj X₀
  let j : Y₀ ⟶ B := (baseChangeIdentityIso q).hom
  let a : (Scheme.pointSmallEtale t).fiber.obj X₀ := Over.homMk t (Category.comp_id t)
  let b : (Scheme.pointSmallEtale s.val).fiber.obj Y₀ :=
    Over.homMk s.val (Category.comp_id s.val)
  have hj : (Scheme.pointSmallEtale s.val).fiber.map j b =
      etalePushforwardGeometricLift q t s X₀ a := by
    let j₀ : Y ⟶ pullback (𝟙 X) q := j.left
    let d : Spec (CommRingCat.of Ω) ⟶ pullback (𝟙 X) q :=
      (etalePushforwardGeometricLift q t s X₀ a).left
    have hj₁ : j₀ ≫ pullback.fst (𝟙 X) q = q := pullback.lift_fst _ _ _
    have hj₂ : j₀ ≫ pullback.snd (𝟙 X) q = 𝟙 Y := pullback.lift_snd _ _ _
    have hd₁ : d ≫ pullback.fst (𝟙 X) q = t := pullback.lift_fst _ _ _
    have hd₂ : d ≫ pullback.snd (𝟙 X) q = s.val := pullback.lift_snd _ _ _
    apply Over.OverMorphism.ext
    change s.val ≫ j₀ = d
    apply pullback.hom_ext
    · rw [Category.assoc, hj₁, hd₁]
      exact s.property
    · rw [Category.assoc, hj₂, hd₂, Category.comp_id]
  refine (toPresheafFiber_etalePushforwardStalkComponent q t s F X₀ a).trans ?_
  change (Scheme.pointSmallEtale s.val).toPresheafFiber B
    (etalePushforwardGeometricLift q t s X₀ a) F.obj =
      F.obj.map j.op ≫ (Scheme.pointSmallEtale s.val).toPresheafFiber Y₀ b F.obj
  rw [(Scheme.pointSmallEtale s.val).toPresheafFiber_w, hj]

end EtaleCohomology
