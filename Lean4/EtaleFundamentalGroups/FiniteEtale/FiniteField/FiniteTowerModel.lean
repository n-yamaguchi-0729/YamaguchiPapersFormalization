/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import EtaleFundamentalGroups.FiniteEtale.FiniteField.ConstantFieldTower
import EtaleFundamentalGroups.FiniteEtale.FiniteField.ConstantFieldLimit
import EtaleFundamentalGroups.FiniteEtale.FiniteField.FiniteFamilyModel
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Finite Tower Model

Two finite coefficient extensions give the model over their actual composite subfield.
-/

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace EtaleFundamentalGroups
variable (k L : Type u) [Field k] [Field L] [Algebra k L]
variable (F : IntermediateField k L) (E : IntermediateField F L)
variable (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))

local notation "φF" => Spec.map (CommRingCat.ofHom (algebraMap k F))
local notation "φE" => Spec.map (CommRingCat.ofHom (algebraMap k E))
local notation "φL" => Spec.map (CommRingCat.ofHom (algebraMap k L))
local notation "η" => Spec.map (CommRingCat.ofHom (algebraMap F E))
local notation "ψF" => Spec.map (CommRingCat.ofHom F.val.toRingHom)
local notation "ψE" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (IntermediateField.val E)))

private theorem finiteIntermediateTowerSpec_comp : η ≫ φF = φE := by
  rw [← Spec.map_comp]
  rfl

/-- Two finite coefficient extensions give the model over their actual composite subfield. -/
def finiteIntermediateTowerIso : pullback η (pullback.fst φF f) ≅ pullback φE f :=
  pullbackRightPullbackFstIso φF f η ≪≫
    pullback.congrHom (finiteIntermediateTowerSpec_comp k L F E) rfl

theorem finiteIntermediateTowerIso_hom_fst :
    (finiteIntermediateTowerIso k L F E X f).hom ≫ pullback.fst φE f =
      pullback.fst η (pullback.fst φF f) := by
  simp only [finiteIntermediateTowerIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
    pullbackRightPullbackFstIso_hom_fst]

theorem finiteIntermediateTowerIso_hom_snd :
    (finiteIntermediateTowerIso k L F E X f).hom ≫ pullback.snd φE f =
      pullback.snd η (pullback.fst φF f) ≫ pullback.snd φF f := by
  simp only [finiteIntermediateTowerIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
    pullbackRightPullbackFstIso_hom_snd]

private theorem finiteIntermediateTowerInclusion_comp : ψE ≫ η = ψF := by
  rw [← Spec.map_comp]
  rfl

/-- The actual coefficient inclusion between the two relative stages. -/
def finiteIntermediateTowerProjection :
    pullback ψF (pullback.fst φF f) ⟶ pullback η (pullback.fst φF f) :=
  pullback.map ψF (pullback.fst φF f) η (pullback.fst φF f)
    ψE (𝟙 _) (𝟙 _) (by rw [Category.comp_id, finiteIntermediateTowerInclusion_comp])
    (by rw [Category.comp_id, Category.id_comp])

/-- For an adjoined finite stage, the relative coefficient inclusion is the
actual leg of the inverse-limit cone. -/
theorem finiteIntermediateTowerProjection_eq_cone (s : Finset L) :
    finiteIntermediateTowerProjection k L F (IntermediateField.adjoin F (s : Set L)) X f =
      (constantFieldInverseLimitCone F L (pullback φF f) (pullback.fst φF f)).π.app
        (Opposite.op s) := by
  apply pullback.hom_ext
  · simp only [finiteIntermediateTowerProjection, pullback.map, pullback.lift_fst]
    exact (constantFieldInverseLimitCone_π_app_fst F L (pullback φF f)
      (pullback.fst φF f) s).symm
  · simp only [finiteIntermediateTowerProjection, pullback.map, pullback.lift_snd,
      Category.comp_id]
    exact (Over.w ((constantFieldInverseLimitOverCone F L (pullback φF f)
      (pullback.fst φF f)).π.app (Opposite.op s))).symm

/-- Flattening finite stages commutes with their literal inclusion into the full extension. -/
theorem finiteIntermediateTowerIso_projection :
    finiteIntermediateTowerProjection k L F E X f ≫
        (finiteIntermediateTowerIso k L F E X f).hom =
      (constantFieldTowerIso k L F X f).hom ≫
        pullback.map φL f φE f
          (Spec.map (CommRingCat.ofHom E.val.toRingHom))
          (𝟙 X) (𝟙 _)
          (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
          (by rw [Category.comp_id, Category.id_comp]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, finiteIntermediateTowerIso_hom_fst,
      finiteIntermediateTowerProjection, pullback.map, pullback.lift_fst]
    rw [← Category.assoc, constantFieldTowerIso_hom_fst]
  · simp only [Category.assoc, finiteIntermediateTowerIso_hom_snd,
      finiteIntermediateTowerProjection, pullback.map, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.comp_id]
    exact (constantFieldTowerIso_hom_snd k L F X f).symm

/-- Recovery over the relative finite stage gives recovery over the same field
viewed as an actual intermediate field of the original extension. -/
def finiteIntermediateTowerModelRecoveryIso
    (N : FiniteEtale (pullback η (pullback.fst φF f)))
    (Z : FiniteEtale (pullback φL f))
    (e : (FiniteEtale.pullback (finiteIntermediateTowerProjection k L F E X f)).obj N ≅
      (FiniteEtale.pullback (constantFieldTowerIso k L F X f).hom).obj Z) :
    (FiniteEtale.pullback (pullback.map φL f φE f ψE (𝟙 X) (𝟙 _)
      (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
      (by rw [Category.comp_id, Category.id_comp]))).obj
        ((FiniteEtale.pullback (finiteIntermediateTowerIso k L F E X f).inv).obj N) ≅ Z := by
  let eX := constantFieldTowerIso k L F X f
  let eY := finiteIntermediateTowerIso k L F E X f
  let cE := finiteIntermediateTowerProjection k L F E X f
  let cH : pullback φL f ⟶ pullback φE f :=
    pullback.map φL f φE f ψE (𝟙 X) (𝟙 _)
      (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
      (by rw [Category.comp_id, Category.id_comp])
  have hn₀ : cE ≫ eY.hom = eX.hom ≫ cH :=
    finiteIntermediateTowerIso_projection k L F E X f
  have hn : cH ≫ eY.inv = eX.inv ≫ cE := by
    apply (cancel_epi eX.hom).mp
    rw [← Category.assoc, ← hn₀, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Iso.hom_inv_id_assoc]
  let eId : (FiniteEtale.pullback (𝟙 (pullback φL f))).obj Z ≅ Z :=
    (FiniteEtale.forget (pullback φL f)).preimageIso
      (Over.pullbackId.app ((FiniteEtale.forget (pullback φL f)).obj Z))
  exact
    FiniteEtale.finiteEtalePullbackCompObjIso cH eY.inv (eX.inv ≫ cE) hn N ≪≫
    (FiniteEtale.finiteEtalePullbackCompObjIso eX.inv cE (eX.inv ≫ cE) rfl N).symm ≪≫
    (FiniteEtale.pullback eX.inv).mapIso e ≪≫
    FiniteEtale.finiteEtalePullbackCompObjIso eX.inv eX.hom (𝟙 _) eX.inv_hom_id Z ≪≫ eId

end EtaleFundamentalGroups
