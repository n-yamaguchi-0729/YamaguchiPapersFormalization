/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import EtaleFundamentalGroups.FiniteEtale.FiniteField.RecoveredCoefficientTransitions
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

/-!
# Recovered Coefficient Recovery

The recovered literal coefficient charts form an actual cover of the input scheme.
-/

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace EtaleFundamentalGroups
variable (k L : Type u) [Field k] [Field L] [Algebra k L]
variable (S : Scheme.{u}) (f : S ⟶ Spec (CommRingCat.of k)) (𝒰 : S.OpenCover)
variable (M : ∀ i : 𝒰.I₀, Over (𝒰.X i))
variable (Z : Over (pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f))
variable (e : ∀ i : 𝒰.I₀,
  (Over.pullback (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (𝒰.f i ≫ f))).obj (M i) ≅
      (Over.pullback ((constantFieldOpenCover k L S f 𝒰).f i)).obj Z)
local notation "φ" => Spec.map (CommRingCat.ofHom (algebraMap k L))
local notation "𝒰L" => constantFieldOpenCover k L S f 𝒰
local notation "ML" => (fun i : 𝒰.I₀ ↦
  Functor.obj (Over.pullback (pullback.snd φ (𝒰.f i ≫ f))) (M i))
local notation "D" => Scheme.Cover.recoveredOverlapGlueData 𝒰L Z ML e

/-- The recovered literal coefficient charts form an actual cover of the input scheme. -/
def recoveredCoefficientChartCover : Z.left.OpenCover :=
  Scheme.Cover.copy (Scheme.Cover.recoveredLocalModelCover 𝒰L Z ML e) 𝒰.I₀
    (fun i ↦ pullback φ (((M i).hom ≫ 𝒰.f i) ≫ f))
    (recoveredCoefficientChartMap k L S f 𝒰 M Z e)
    (Equiv.refl _) (fun i ↦ (modelTotalIso φ f (𝒰.f i) (M i).hom).symm)
    (fun _ ↦ rfl)

/-- The literal coefficient overlap is the actual intersection of the two
recovered literal charts in the input scheme. -/
theorem recoveredCoefficientTransition_isPullback (i j : 𝒰.I₀) :
    IsPullback (coefficientOverlapFirstMap φ f (𝒰.f i) (𝒰.f j) (M i).hom)
      (recoveredCoefficientTransition k L S f 𝒰 M Z e i j ≫
        coefficientOverlapFirstMap φ f (𝒰.f j) (𝒰.f i) (M j).hom)
      (recoveredCoefficientChartMap k L S f 𝒰 M Z e i)
      (recoveredCoefficientChartMap k L S f 𝒰 M Z e j) := by
  have hp (i j : 𝒰.I₀) :
      (recoveredCoefficientOverlapIso k L S f 𝒰 M Z e i j).hom ≫ (D).f i j =
        coefficientOverlapFirstMap φ f (𝒰.f i) (𝒰.f j) (M i).hom ≫
          (modelTotalIso φ f (𝒰.f i) (M i).hom).inv := by
    have h := congrArg (fun q ↦ q ≫ (modelTotalIso φ f (𝒰.f i) (M i).hom).inv)
      (modelOverlapIso_hom_first φ f (𝒰.f i) (𝒰.f j) (M i).hom)
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
    exact h
  refine (Scheme.Cover.recoveredOverlapGlueData_isPullback 𝒰L Z ML e i j).of_iso'
    (recoveredCoefficientOverlapIso k L S f 𝒰 M Z e i j)
    (modelTotalIso φ f (𝒰.f i) (M i).hom).symm
    (modelTotalIso φ f (𝒰.f j) (M j).hom).symm (Iso.refl _) (hp i j) ?_ ?_ ?_
  · have he : (recoveredCoefficientOverlapIso k L S f 𝒰 M Z e j i).inv ≫
        coefficientOverlapFirstMap φ f (𝒰.f j) (𝒰.f i) (M j).hom ≫
          (modelTotalIso φ f (𝒰.f j) (M j).hom).inv = (D).f j i := by
      rw [← hp j i]
      exact Iso.inv_hom_id_assoc _ _
    let t' :
        pullback (pullback.snd (M i).hom (pullback.snd φ (𝒰.f i ≫ f)) ≫
          coefficientModelMap φ f (𝒰.f i)) (coefficientModelMap φ f (𝒰.f j)) ⟶
        pullback (pullback.snd (M j).hom (pullback.snd φ (𝒰.f j ≫ f)) ≫
          coefficientModelMap φ f (𝒰.f j)) (coefficientModelMap φ f (𝒰.f i)) := (D).t i j
    have he' : (modelOverlapIso φ f (𝒰.f j) (𝒰.f i) (M j).hom).inv ≫
        coefficientOverlapFirstMap φ f (𝒰.f j) (𝒰.f i) (M j).hom ≫
          (modelTotalIso φ f (𝒰.f j) (M j).hom).inv =
        pullback.fst (pullback.snd (M j).hom (pullback.snd φ (𝒰.f j ≫ f)) ≫
          coefficientModelMap φ f (𝒰.f j)) (coefficientModelMap φ f (𝒰.f i)) := he
    change (modelOverlapIso φ f (𝒰.f i) (𝒰.f j) (M i).hom).hom ≫ t' ≫
      pullback.fst _ _ =
      (((modelOverlapIso φ f (𝒰.f i) (𝒰.f j) (M i).hom).hom ≫ t' ≫
        (modelOverlapIso φ f (𝒰.f j) (𝒰.f i) (M j).hom).inv) ≫
        coefficientOverlapFirstMap φ f (𝒰.f j) (𝒰.f i) (M j).hom) ≫
          (modelTotalIso φ f (𝒰.f j) (M j).hom).inv
    simp only [Category.assoc, he']
  · exact (Category.comp_id _).symm
  · exact (Category.comp_id _).symm

end EtaleFundamentalGroups
