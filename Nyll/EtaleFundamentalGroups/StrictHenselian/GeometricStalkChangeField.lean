/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Extending the field of a pointed étale colimit

Compose each actual field-valued neighborhood point with the given field
embedding. The existing colimit descent constructs the map on stalks. Its
evaluation and structure-map equations are proved on the original germ maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω Ω' : Type u} [CommRing R] [Field Ω] [Field Ω']
  (φ : R →+* Ω) (ι : Ω →+* Ω')

/-- The same actual étale neighborhood pointed over the larger field. -/
def pointedEtaleChangeField (W : (Spec (.of R)).Etale)
    (t : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj W) :
    (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom (ι.comp φ)))).fiber.obj W :=
  Over.homMk (Spec.map (CommRingCat.ofHom ι) ≫ t.left) (by
    rw [Category.assoc, t.w]
    exact (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ι)).symm)

theorem pointedEtaleChangeField_naturality
    {W V : (Spec (.of R)).Etale} (g : W ⟶ V)
    (t : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj W) :
    (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom (ι.comp φ)))).fiber.map g
        (pointedEtaleChangeField φ ι W t) =
      pointedEtaleChangeField φ ι V
        ((Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.map g t) := by
  apply Over.OverMorphism.ext
  exact Category.assoc _ _ _

/-- Field extension induces the actual map between the existing pointed
étale colimits; no second colimit construction is introduced. -/
def geometricStalkChangeField :
    geometricStalk (Spec.map (CommRingCat.ofHom φ)) ⟶
      geometricStalk (Spec.map (CommRingCat.ofHom (ι.comp φ))) :=
  (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).presheafFiberDesc
    (fun W t => geometricStalkGerm (Spec.map (CommRingCat.ofHom (ι.comp φ))) W
      (pointedEtaleChangeField φ ι W t)) (by
      intro W V g t
      have h := (Scheme.pointEtaleNeighborhoods
        (Spec.map (CommRingCat.ofHom (ι.comp φ)))).toPresheafFiber_w
          g (pointedEtaleChangeField φ ι W t) (etaleSections (Spec (.of R)))
      rw [pointedEtaleChangeField_naturality] at h
      exact h)

/-- The induced map sends every germ to the germ with its extended point. -/
theorem geometricStalkGerm_changeField (W : (Spec (.of R)).Etale)
    (t : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj W) :
    geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W t ≫
        geometricStalkChangeField φ ι =
      geometricStalkGerm (Spec.map (CommRingCat.ofHom (ι.comp φ))) W
        (pointedEtaleChangeField φ ι W t) :=
  (Scheme.pointEtaleNeighborhoods
    (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber_presheafFiberDesc _ _ W t

/-- Evaluation of the colimit map is the prescribed field embedding. -/
theorem geometricStalkChangeField_evaluation :
    geometricStalkChangeField φ ι ≫
        geometricStalkEvaluation (Spec.map (CommRingCat.ofHom (ι.comp φ))) =
      geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ)) ≫
        CommRingCat.ofHom ι := by
  apply (Scheme.pointEtaleNeighborhoods
    (Spec.map (CommRingCat.ofHom φ))).presheafFiber_hom_ext
  intro W t
  change geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W t ≫
      geometricStalkChangeField φ ι ≫
        geometricStalkEvaluation (Spec.map (CommRingCat.ofHom (ι.comp φ))) =
    geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W t ≫
      geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ)) ≫ CommRingCat.ofHom ι
  rw [← Category.assoc, geometricStalkGerm_changeField,
    geometricStalkGerm_evaluation]
  change (Spec.map (CommRingCat.ofHom ι) ≫ t.left).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom = _
  rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
    ← Category.assoc, ← geometricStalkGerm_evaluation]
  exact Category.assoc (geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W t)
    (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))) (CommRingCat.ofHom ι)

theorem geometricStalkChangeField_evaluation_apply
    (a : geometricStalk (Spec.map (CommRingCat.ofHom φ))) :
    geometricStalkEvaluation (Spec.map (CommRingCat.ofHom (ι.comp φ)))
        (geometricStalkChangeField φ ι a) =
      ι (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ)) a) :=
  ConcreteCategory.congr_hom (geometricStalkChangeField_evaluation φ ι) a

/-- The field-extension map preserves the original base-ring structure. -/
theorem geometricStalkChangeField_comp_structure :
    (geometricStalkChangeField φ ι).hom.comp (geometricStalkStructureMap φ) =
      geometricStalkStructureMap (ι.comp φ) := by
  let W : (Spec (.of R)).Etale := Scheme.Etale.mk (𝟙 (Spec (.of R)))
  let t : (Scheme.pointEtaleNeighborhoods
      (Spec.map (CommRingCat.ofHom φ))).fiber.obj W :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ)) (Category.comp_id _)
  let t' : (Scheme.pointEtaleNeighborhoods
      (Spec.map (CommRingCat.ofHom (ι.comp φ)))).fiber.obj W :=
    Over.homMk (Spec.map (CommRingCat.ofHom (ι.comp φ))) (Category.comp_id _)
  have ht : pointedEtaleChangeField φ ι W t = t' := by
    apply Over.OverMorphism.ext
    exact (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ι)).symm
  let γ : Γ(Spec (.of R), ⊤) ⟶ geometricStalk (Spec.map (CommRingCat.ofHom φ)) :=
    geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W t
  let γ' : Γ(Spec (.of R), ⊤) ⟶
      geometricStalk (Spec.map (CommRingCat.ofHom (ι.comp φ))) :=
    geometricStalkGerm (Spec.map (CommRingCat.ofHom (ι.comp φ))) W t'
  have hγ : γ ≫ geometricStalkChangeField φ ι = γ' :=
    (geometricStalkGerm_changeField φ ι W t).trans
      (congrArg (geometricStalkGerm (Spec.map (CommRingCat.ofHom (ι.comp φ))) W) ht)
  have hcat : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ γ) ≫
      geometricStalkChangeField φ ι = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ γ' :=
    (Category.assoc _ _ _).trans
      (congrArg (fun k : Γ(Spec (.of R), ⊤) ⟶
        geometricStalk (Spec.map (CommRingCat.ofHom (ι.comp φ))) =>
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ k) hγ)
  exact congrArg CommRingCat.Hom.hom hcat

/-- Extending the pointing field gives a local map of the constructed stalks. -/
instance geometricStalkChangeField_isLocalHom :
    IsLocalHom (geometricStalkChangeField φ ι).hom where
  map_nonunit a ha := by
    apply geometricStalk_isUnit_of_evaluation_ne_zero
      (Spec.map (CommRingCat.ofHom φ)) a
    intro hzero
    apply (ha.map (geometricStalkEvaluation
      (Spec.map (CommRingCat.ofHom (ι.comp φ)))).hom).ne_zero
    rw [geometricStalkChangeField_evaluation_apply, hzero, map_zero]

end EtaleFundamentalGroups.StrictHenselian
