/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import EtaleFundamentalGroups.FiniteEtale.FiniteField.ModelOverlap
import EtaleFundamentalGroups.FiniteEtale.FiniteField.RecoveredOverlap
import EtaleFundamentalGroups.FiniteEtale.FiniteField.ConstantFieldCover
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Coefficient transitions for recovered local models

Recovered overlap maps are transported to literal coefficient extensions.
Their transitions preserve the coefficient projections and recover the original
chart maps.
-/

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace EtaleFundamentalGroups

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
variable (S : Scheme.{u}) (f : S ⟶ Spec (CommRingCat.of k)) (𝒰 : S.OpenCover)
variable (M : ∀ i : 𝒰.I₀, Over (𝒰.X i))
local notation "φ" => Spec.map (CommRingCat.ofHom (algebraMap k L))
local notation "𝒰L" => constantFieldOpenCover k L S f 𝒰
local notation "ML" => (fun i : 𝒰.I₀ ↦
  Functor.obj (Over.pullback (pullback.snd φ (𝒰.f i ≫ f))) (M i))
variable (Z : Over (pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f))
variable (e : ∀ i : 𝒰.I₀,
  (Over.pullback (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (𝒰.f i ≫ f))).obj (M i) ≅
      (Over.pullback ((constantFieldOpenCover k L S f 𝒰).f i)).obj Z)
local notation "D" => Scheme.Cover.recoveredOverlapGlueData 𝒰L Z ML e
local notation "a" => (fun i : 𝒰.I₀ ↦ Comma.hom (M i) ≫ 𝒰.f i)
local notation "v" => (fun i j : 𝒰.I₀ ↦ pullback.fst (a i) (𝒰.f j) ≫ a i)

/-- Identify a literal coefficient-extended overlap with the recovered gluing overlap. -/
def recoveredCoefficientOverlapIso (i j : 𝒰.I₀) :
    pullback φ (v i j ≫ f) ≅ (D).V (i, j) :=
  modelOverlapIso φ f (𝒰.f i) (𝒰.f j) (M i).hom

theorem recoveredCoefficientOverlapIso_base (i j : 𝒰.I₀) :
    (recoveredCoefficientOverlapIso k L S f 𝒰 M Z e i j).hom ≫
        (D).f i j ≫ (ML i).hom ≫ (𝒰L).f i = coefficientModelMap φ f (v i j) :=
  modelOverlapIso_hom_base φ f (𝒰.f i) (𝒰.f j) (M i).hom

/-- Transport the recovered transition to the literal coefficient-extended overlaps. -/
def recoveredCoefficientTransition (i j : 𝒰.I₀) :
    pullback φ (v i j ≫ f) ⟶ pullback φ (v j i ≫ f) :=
  (recoveredCoefficientOverlapIso k L S f 𝒰 M Z e i j).hom ≫ (D).t i j ≫
    (recoveredCoefficientOverlapIso k L S f 𝒰 M Z e j i).inv

theorem recoveredCoefficientTransition_base (i j : 𝒰.I₀) :
    recoveredCoefficientTransition k L S f 𝒰 M Z e i j ≫
        coefficientModelMap φ f (v j i) = coefficientModelMap φ f (v i j) := by
  have he : (recoveredCoefficientOverlapIso k L S f 𝒰 M Z e j i).inv ≫
      coefficientModelMap φ f (v j i) = (D).f j i ≫ (ML j).hom ≫ (𝒰L).f j := by
    rw [← recoveredCoefficientOverlapIso_base k L S f 𝒰 M Z e j i,
      Iso.inv_hom_id_assoc]
  simp only [recoveredCoefficientTransition, Category.assoc, he]
  exact (congrArg (fun q ↦ (recoveredCoefficientOverlapIso k L S f 𝒰 M Z e i j).hom ≫ q)
    (Scheme.Cover.recoveredOverlapGlueData_transition_base 𝒰L Z ML e i j)).trans
      (recoveredCoefficientOverlapIso_base k L S f 𝒰 M Z e i j)

theorem recoveredCoefficientTransition_coefficient (i j : 𝒰.I₀) :
    recoveredCoefficientTransition k L S f 𝒰 M Z e i j ≫
        pullback.fst φ (v j i ≫ f) = pullback.fst φ (v i j ≫ f) := by
  have h := congrArg (fun q ↦ q ≫ pullback.fst φ f)
    (recoveredCoefficientTransition_base k L S f 𝒰 M Z e i j)
  simpa only [Category.assoc, coefficientModelMap, pullback.lift_fst] using h

theorem recoveredCoefficientTransition_original (i j : 𝒰.I₀) :
    recoveredCoefficientTransition k L S f 𝒰 M Z e i j ≫
        pullback.snd φ (v j i ≫ f) ≫ v j i = pullback.snd φ (v i j ≫ f) ≫ v i j := by
  have h := congrArg (fun q ↦ q ≫ pullback.snd φ f)
    (recoveredCoefficientTransition_base k L S f 𝒰 M Z e i j)
  simpa only [Category.assoc, coefficientModelMap, pullback.lift_snd] using h

/-- The original recovered chart map expressed on the literal coefficient extension. -/
def recoveredCoefficientChartMap (i : 𝒰.I₀) :
    pullback φ (a i ≫ f) ⟶ Z.left :=
  (modelTotalIso φ f (𝒰.f i) (M i).hom).inv ≫
    Scheme.Cover.recoveredLocalModelMap 𝒰L Z ML e i

theorem recoveredCoefficientChartMap_isOpenImmersion (i : 𝒰.I₀) :
    IsOpenImmersion (recoveredCoefficientChartMap k L S f 𝒰 M Z e i) := by
  let h : pullback (M i).hom (pullback.snd φ (𝒰.f i ≫ f)) ⟶ Z.left :=
    Scheme.Cover.recoveredLocalModelMap 𝒰L Z ML e i
  let : IsOpenImmersion h :=
    (Scheme.Cover.recoveredLocalModelCover 𝒰L Z ML e).map_prop i
  change IsOpenImmersion ((modelTotalIso φ f (𝒰.f i) (M i).hom).inv ≫ h)
  infer_instance

theorem recoveredCoefficientOverlapIso_chartMap (i j : 𝒰.I₀) :
    (recoveredCoefficientOverlapIso k L S f 𝒰 M Z e i j).hom ≫
        (D).f i j ≫ Scheme.Cover.recoveredLocalModelMap 𝒰L Z ML e i =
      coefficientOverlapFirstMap φ f (𝒰.f i) (𝒰.f j) (M i).hom ≫
        recoveredCoefficientChartMap k L S f 𝒰 M Z e i := by
  let c : pullback (M i).hom (pullback.snd φ (𝒰.f i ≫ f)) ⟶ Z.left :=
    Scheme.Cover.recoveredLocalModelMap 𝒰L Z ML e i
  have h := congrArg (fun q ↦ q ≫ (modelTotalIso φ f (𝒰.f i) (M i).hom).inv ≫ c)
      (modelOverlapIso_hom_first φ f (𝒰.f i) (𝒰.f j) (M i).hom)
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at h
  exact h

/-- The literal coefficient transitions recover the same map to the original cover. -/
theorem recoveredCoefficientTransition_chartMap (i j : 𝒰.I₀) :
    recoveredCoefficientTransition k L S f 𝒰 M Z e i j ≫
        coefficientOverlapFirstMap φ f (𝒰.f j) (𝒰.f i) (M j).hom ≫
          recoveredCoefficientChartMap k L S f 𝒰 M Z e j =
      coefficientOverlapFirstMap φ f (𝒰.f i) (𝒰.f j) (M i).hom ≫
        recoveredCoefficientChartMap k L S f 𝒰 M Z e i := by
  have he : (recoveredCoefficientOverlapIso k L S f 𝒰 M Z e j i).inv ≫
      coefficientOverlapFirstMap φ f (𝒰.f j) (𝒰.f i) (M j).hom ≫
        recoveredCoefficientChartMap k L S f 𝒰 M Z e j =
      (D).f j i ≫ Scheme.Cover.recoveredLocalModelMap 𝒰L Z ML e j := by
    rw [← recoveredCoefficientOverlapIso_chartMap k L S f 𝒰 M Z e j i,
      Iso.inv_hom_id_assoc]
  simp only [recoveredCoefficientTransition, Category.assoc, he]
  exact (congrArg (fun q ↦ (recoveredCoefficientOverlapIso k L S f 𝒰 M Z e i j).hom ≫ q)
    (Scheme.Cover.recoveredOverlapGlueData_transition_map 𝒰L Z ML e i j)).trans
      (recoveredCoefficientOverlapIso_chartMap k L S f 𝒰 M Z e i j)

end EtaleFundamentalGroups
