/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import EtaleFundamentalGroups.FiniteEtale.FiniteField.ModelOverlap
import EtaleFundamentalGroups.FiniteEtale.FiniteField.SchemePairDescent
import SchemeTheory.FiniteEtale.Basic

/-!
# Raw Overlap Supplier

The literal coefficient extension of a local model, over its coefficient base.
-/

noncomputable section
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
namespace EtaleFundamentalGroups
variable {T T' S U V Y : Scheme.{u}}
variable (φ : T' ⟶ T) (f : S ⟶ T) (u : U ⟶ S) (v : V ⟶ S) (y : Y ⟶ U)

/-- The literal coefficient extension of a local model, over its coefficient base. -/
abbrev coefficientLocalModelOver : Over T' :=
  Over.mk (pullback.fst φ ((y ≫ u) ≫ f))

/-- The literal coefficient extension of an overlap, over its coefficient base. -/
abbrev coefficientOverlapOver : Over T' :=
  Over.mk (pullback.fst φ ((pullback.fst (y ≫ u) v ≫ (y ≫ u)) ≫ f))

/-- The literal coefficient extension of the first overlap inclusion. -/
def coefficientOverlapInclusion :
    coefficientOverlapOver φ f u v y ⟶ coefficientLocalModelOver φ f u y :=
  Over.homMk (coefficientOverlapFirstMap φ f u v y) (pullback.lift_fst _ _ _)

/-- The actual local-model map to the coefficient-extended base chart. -/
def coefficientLocalModelStructure :
    (coefficientLocalModelOver φ f u y).left ⟶ pullback φ (u ≫ f) :=
  (modelTotalIso φ f u y).inv ≫ pullback.snd y (pullback.snd φ (u ≫ f))

/-- The actual second map of the coefficient-extended overlap. -/
def coefficientOverlapSecondMap :
    (coefficientOverlapOver φ f u v y).left ⟶ pullback φ (v ≫ f) :=
  (modelOverlapIso φ f u v y).hom ≫ pullback.snd _ _

/-- The raw coefficient-extended overlap is cartesian over the extended cover. -/
theorem coefficientOverlap_isPullback :
    IsPullback (coefficientOverlapInclusion φ f u v y).left
      (coefficientOverlapSecondMap φ f u v y)
      (coefficientLocalModelStructure φ f u y ≫ coefficientModelMap φ f u)
      (coefficientModelMap φ f v) := by
  refine (IsPullback.of_hasPullback
    (pullback.snd y (pullback.snd φ (u ≫ f)) ≫ coefficientModelMap φ f u)
    (coefficientModelMap φ f v)).of_iso'
    (modelOverlapIso φ f u v y) (modelTotalIso φ f u y).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change (modelOverlapIso φ f u v y).hom ≫ pullback.fst _ _ =
      coefficientOverlapFirstMap φ f u v y ≫ (modelTotalIso φ f u y).inv
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun q => q ≫ (modelTotalIso φ f u y).inv)
        (modelOverlapIso_hom_first φ f u v y)
  · exact (Category.comp_id _).symm
  · simp only [Iso.symm_hom, Iso.refl_hom, coefficientLocalModelStructure,
      Category.comp_id, Category.assoc]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The local model structure is the actual base change of the original one. -/
theorem coefficientLocalModelStructure_isPullback :
    IsPullback (coefficientLocalModelStructure φ f u y)
      (pullback.snd φ ((y ≫ u) ≫ f))
      (pullback.snd φ (u ≫ f)) y := by
  refine (IsPullback.of_hasPullback y (pullback.snd φ (u ≫ f))).flip.of_iso'
    (modelTotalIso φ f u y).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.symm_hom, Iso.refl_hom, coefficientLocalModelStructure, Category.comp_id]
  · change (modelTotalIso φ f u y).inv ≫ pullback.fst y (pullback.snd φ (u ≫ f)) =
      pullback.snd φ ((y ≫ u) ≫ f) ≫ 𝟙 Y
    rw [Category.comp_id, ← modelTotalIso_hom_snd, Iso.inv_hom_id_assoc]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- Actual finite étale local models remain finite étale on the literal extension. -/
theorem coefficientLocalModelStructure_finiteEtale [IsFiniteEtale y] :
    IsFiniteEtale (coefficientLocalModelStructure φ f u y) :=
  MorphismProperty.of_isPullback
    (P := (show MorphismProperty Scheme.{u} from @IsFiniteEtale))
    (coefficientLocalModelStructure_isPullback φ f u y).flip inferInstance

/-- The local structure and chart inclusion agree with the literal total-model map. -/
theorem coefficientLocalModelStructure_base :
    coefficientLocalModelStructure φ f u y ≫ coefficientModelMap φ f u =
      coefficientModelMap φ f (y ≫ u) := by
  rw [coefficientLocalModelStructure, Category.assoc, modelTotalIso_inv_coefficientModelMap]

/-- The first overlap inclusion preserves the actual map to the extended base. -/
theorem coefficientOverlapInclusion_base :
    (coefficientOverlapInclusion φ f u v y).left ≫
        coefficientLocalModelStructure φ f u y ≫ coefficientModelMap φ f u =
      coefficientModelMap φ f (pullback.fst (y ≫ u) v ≫ (y ≫ u)) := by
  change coefficientOverlapFirstMap φ f u v y ≫
    coefficientLocalModelStructure φ f u y ≫ coefficientModelMap φ f u = _
  rw [← modelOverlapIso_hom_first, coefficientLocalModelStructure]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact modelOverlapIso_hom_base φ f u v y

section FieldStage
variable (k L : Type u) [Field k] [Field L] [Algebra k L]
variable (S U V Y : Scheme.{u}) (f : S ⟶ Spec (CommRingCat.of k))
variable (u : U ⟶ S) (v : V ⟶ S) (y : Y ⟶ U) (s : Finset L)

local notation "φL" => Spec.map (CommRingCat.ofHom (algebraMap k L))
local notation "φE" => Spec.map (CommRingCat.ofHom
  (algebraMap k (IntermediateField.adjoin k (s : Set L))))
local notation "p" => (pullback.fst (y ≫ u) v ≫ (y ≫ u))

/-- The actual coefficient cone maps preserve the first overlap inclusions. -/
theorem coefficientOverlapFirstMap_stage_naturality :
    (constantFieldInverseLimitCone k L (pullback (y ≫ u) v) (p ≫ f)).π.app (op s) ≫
        coefficientOverlapFirstMap φE f u v y =
      coefficientOverlapFirstMap φL f u v y ≫
        (constantFieldInverseLimitCone k L Y ((y ≫ u) ≫ f)).π.app (op s) := by
  let rV : pullback φL (p ≫ f) ⟶ pullback φE (p ≫ f) :=
    (constantFieldInverseLimitCone k L (pullback (y ≫ u) v) (p ≫ f)).π.app (op s)
  let rA : pullback φL ((y ≫ u) ≫ f) ⟶ pullback φE ((y ≫ u) ≫ f) :=
    (constantFieldInverseLimitCone k L Y ((y ≫ u) ≫ f)).π.app (op s)
  have hv : rV ≫ pullback.fst φE (p ≫ f) = pullback.fst φL (p ≫ f) ≫
      Spec.map (CommRingCat.ofHom (IntermediateField.adjoin k (s : Set L)).val.toRingHom) :=
    constantFieldInverseLimitCone_π_app_fst k L (pullback (y ≫ u) v) (p ≫ f) s
  have ha : rA ≫ pullback.fst φE ((y ≫ u) ≫ f) = pullback.fst φL ((y ≫ u) ≫ f) ≫
      Spec.map (CommRingCat.ofHom (IntermediateField.adjoin k (s : Set L)).val.toRingHom) :=
    constantFieldInverseLimitCone_π_app_fst k L Y ((y ≫ u) ≫ f) s
  have hvs : rV ≫ pullback.snd φE (p ≫ f) = pullback.snd φL (p ≫ f) :=
    Over.w ((constantFieldInverseLimitOverCone k L (pullback (y ≫ u) v) (p ≫ f)).π.app (op s))
  have has : rA ≫ pullback.snd φE ((y ≫ u) ≫ f) = pullback.snd φL ((y ≫ u) ≫ f) :=
    Over.w ((constantFieldInverseLimitOverCone k L Y ((y ≫ u) ≫ f)).π.app (op s))
  change rV ≫ coefficientOverlapFirstMap φE f u v y =
    coefficientOverlapFirstMap φL f u v y ≫ rA
  apply pullback.hom_ext
  · simp only [Category.assoc, coefficientOverlapFirstMap, pullback.lift_fst]
    rw [ha, pullback.lift_fst_assoc, hv]
  · simp only [Category.assoc, coefficientOverlapFirstMap, pullback.lift_snd]
    rw [has, pullback.lift_snd, reassoc_of% hvs]

end FieldStage
end EtaleFundamentalGroups
