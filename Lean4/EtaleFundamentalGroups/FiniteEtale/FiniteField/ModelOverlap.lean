/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import EtaleFundamentalGroups.FiniteEtale.FiniteField.CoefficientPullback

/-!
# Pullback comparisons for coefficient-extended models

The total-space and overlap comparisons identify coefficient extension with
iterated pullbacks and preserve the original projections and maps to the base.
-/

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace EtaleFundamentalGroups

variable {T T' S U V Y : Scheme.{u}}
variable (φ : T' ⟶ T) (f : S ⟶ T) (u : U ⟶ S) (v : V ⟶ S) (y : Y ⟶ U)

/-- The literal coefficient extension of a map to the base scheme. -/
abbrev coefficientModelMap {A : Scheme.{u}} (a : A ⟶ S) :
    pullback φ (a ≫ f) ⟶ pullback φ f :=
  pullback.lift (pullback.fst φ (a ≫ f)) (pullback.snd φ (a ≫ f) ≫ a)
    (by rw [Category.assoc]; exact pullback.condition)

/-- Compare the iterated total-space pullback with the literal coefficient extension. -/
def modelTotalIso :
    pullback y (pullback.snd φ (u ≫ f)) ≅ pullback φ ((y ≫ u) ≫ f) :=
  pullbackSymmetry y (pullback.snd φ (u ≫ f)) ≪≫
    pullbackLeftPullbackSndIso φ (u ≫ f) y ≪≫
      pullback.congrHom rfl (Category.assoc y u f).symm

theorem modelTotalIso_hom_fst :
    (modelTotalIso φ f u y).hom ≫ pullback.fst φ ((y ≫ u) ≫ f) =
      pullback.snd y (pullback.snd φ (u ≫ f)) ≫ pullback.fst φ (u ≫ f) := by
  simp only [modelTotalIso, Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
    pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst,
    pullbackSymmetry_hom_comp_fst_assoc]

theorem modelTotalIso_hom_snd :
    (modelTotalIso φ f u y).hom ≫ pullback.snd φ ((y ≫ u) ≫ f) =
      pullback.fst y (pullback.snd φ (u ≫ f)) := by
  simp only [modelTotalIso, Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
    pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd,
    pullbackSymmetry_hom_comp_snd]

theorem modelTotalIso_hom_coefficientModelMap :
    (modelTotalIso φ f u y).hom ≫ coefficientModelMap φ f (y ≫ u) =
      pullback.snd y (pullback.snd φ (u ≫ f)) ≫ coefficientModelMap φ f u := by
  apply pullback.hom_ext
  · simp only [coefficientModelMap, Category.assoc, pullback.lift_fst]
    exact modelTotalIso_hom_fst φ f u y
  · simp only [coefficientModelMap, Category.assoc, pullback.lift_snd]
    rw [← Category.assoc, modelTotalIso_hom_snd]
    rw [← Category.assoc, pullback.condition, Category.assoc]

theorem modelTotalIso_inv_coefficientModelMap :
    (modelTotalIso φ f u y).inv ≫
        (pullback.snd y (pullback.snd φ (u ≫ f)) ≫ coefficientModelMap φ f u) =
      coefficientModelMap φ f (y ≫ u) := by
  rw [← modelTotalIso_hom_coefficientModelMap, Iso.inv_hom_id_assoc]

/-- Compare the literal coefficient overlap with the pullback of extended chart models. -/
def modelOverlapIso :
    pullback φ ((pullback.fst (y ≫ u) v ≫ (y ≫ u)) ≫ f) ≅
      pullback (pullback.snd y (pullback.snd φ (u ≫ f)) ≫ coefficientModelMap φ f u)
        (coefficientModelMap φ f v) := by
  let m := pullback.map (coefficientModelMap φ f (y ≫ u)) (coefficientModelMap φ f v)
    (pullback.snd y (pullback.snd φ (u ≫ f)) ≫ coefficientModelMap φ f u)
    (coefficientModelMap φ f v) (modelTotalIso φ f u y).inv (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, modelTotalIso_inv_coefficientModelMap])
    (by rw [Category.comp_id, Category.id_comp])
  haveI : IsIso m := by dsimp only [m]; infer_instance
  let em := asIso m
  exact pullback.congrHom rfl (Category.assoc _ _ _) ≪≫
    coefficientPullbackIso φ f (y ≫ u) v ≪≫
      em

theorem modelOverlapIso_hom_first_original :
    (modelOverlapIso φ f u v y).hom ≫
      pullback.fst (pullback.snd y (pullback.snd φ (u ≫ f)) ≫ coefficientModelMap φ f u)
        (coefficientModelMap φ f v) ≫
        pullback.fst y (pullback.snd φ (u ≫ f)) =
      pullback.snd φ ((pullback.fst (y ≫ u) v ≫ (y ≫ u)) ≫ f) ≫
        pullback.fst (y ≫ u) v := by
  have he : (modelTotalIso φ f u y).inv ≫
      pullback.fst y (pullback.snd φ (u ≫ f)) =
      pullback.snd φ ((y ≫ u) ≫ f) := by
    rw [← modelTotalIso_hom_snd, Iso.inv_hom_id_assoc]
  simp only [modelOverlapIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullback.map, pullback.lift_fst_assoc, he]
  rw [reassoc_of% (coefficientPullbackIso_hom_fst φ f (y ≫ u) v)]
  simp only [pullback.lift_snd, pullback.congrHom_hom, Category.assoc,
    pullback.lift_snd_assoc, Category.id_comp]

theorem modelOverlapIso_hom_second_original :
    (modelOverlapIso φ f u v y).hom ≫
      pullback.snd (pullback.snd y (pullback.snd φ (u ≫ f)) ≫ coefficientModelMap φ f u)
        (coefficientModelMap φ f v) ≫
        pullback.snd φ (v ≫ f) =
      pullback.snd φ ((pullback.fst (y ≫ u) v ≫ (y ≫ u)) ≫ f) ≫
        pullback.snd (y ≫ u) v := by
  simp only [modelOverlapIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullback.map, pullback.lift_snd_assoc, Category.id_comp]
  rw [reassoc_of% (coefficientPullbackIso_hom_snd φ f (y ≫ u) v)]
  simp only [pullback.lift_snd, pullback.congrHom_hom, Category.assoc,
    pullback.lift_snd_assoc, Category.id_comp]

theorem modelOverlapIso_hom_coefficient :
    (modelOverlapIso φ f u v y).hom ≫
      pullback.fst (pullback.snd y (pullback.snd φ (u ≫ f)) ≫ coefficientModelMap φ f u)
        (coefficientModelMap φ f v) ≫
        pullback.snd y (pullback.snd φ (u ≫ f)) ≫ pullback.fst φ (u ≫ f) =
      pullback.fst φ ((pullback.fst (y ≫ u) v ≫ (y ≫ u)) ≫ f) := by
  have he : (modelTotalIso φ f u y).inv ≫
      pullback.snd y (pullback.snd φ (u ≫ f)) ≫ pullback.fst φ (u ≫ f) =
      pullback.fst φ ((y ≫ u) ≫ f) := by
    rw [← modelTotalIso_hom_fst, Iso.inv_hom_id_assoc]
  simp only [modelOverlapIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullback.map, pullback.lift_fst_assoc, he]
  rw [reassoc_of% (coefficientPullbackIso_hom_fst φ f (y ≫ u) v)]
  simp only [pullback.lift_fst, pullback.congrHom_hom, Category.comp_id]

theorem modelOverlapIso_hom_base :
    (modelOverlapIso φ f u v y).hom ≫
      pullback.fst (pullback.snd y (pullback.snd φ (u ≫ f)) ≫ coefficientModelMap φ f u)
        (coefficientModelMap φ f v) ≫
        pullback.snd y (pullback.snd φ (u ≫ f)) ≫ coefficientModelMap φ f u =
      coefficientModelMap φ f (pullback.fst (y ≫ u) v ≫ (y ≫ u)) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, coefficientModelMap, pullback.lift_fst]
    exact modelOverlapIso_hom_coefficient φ f u v y
  · simp only [Category.assoc, coefficientModelMap, pullback.lift_snd]
    rw [← pullback.condition_assoc]
    rw [reassoc_of% (modelOverlapIso_hom_first_original φ f u v y)]

/-- The literal first projection of a coefficient-extended overlap. -/
def coefficientOverlapFirstMap :
    pullback φ ((pullback.fst (y ≫ u) v ≫ (y ≫ u)) ≫ f) ⟶
      pullback φ ((y ≫ u) ≫ f) :=
  pullback.lift (pullback.fst φ ((pullback.fst (y ≫ u) v ≫ (y ≫ u)) ≫ f))
    (pullback.snd φ ((pullback.fst (y ≫ u) v ≫ (y ≫ u)) ≫ f) ≫
      pullback.fst (y ≫ u) v)
    (by rw [Category.assoc, ← Category.assoc (pullback.fst (y ≫ u) v)];
        exact pullback.condition)

/-- The overlap comparison identifies the first projection with literal
coefficient extension of the original projection. -/
theorem modelOverlapIso_hom_first :
    (modelOverlapIso φ f u v y).hom ≫
        pullback.fst (pullback.snd y (pullback.snd φ (u ≫ f)) ≫ coefficientModelMap φ f u)
          (coefficientModelMap φ f v) ≫ (modelTotalIso φ f u y).hom =
      coefficientOverlapFirstMap φ f u v y := by
  apply pullback.hom_ext
  · simp only [Category.assoc, modelTotalIso_hom_fst,
      coefficientOverlapFirstMap, pullback.lift_fst]
    exact modelOverlapIso_hom_coefficient φ f u v y
  · simp only [Category.assoc, modelTotalIso_hom_snd,
      coefficientOverlapFirstMap, pullback.lift_snd]
    exact modelOverlapIso_hom_first_original φ f u v y

end EtaleFundamentalGroups
