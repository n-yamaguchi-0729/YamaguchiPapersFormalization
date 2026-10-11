/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import SchemeTheory.Gluing.RecoveredPullback
import EtaleFundamentalGroups.FiniteEtale.FiniteField.RawStageGlue
import EtaleFundamentalGroups.FiniteEtale.FiniteField.RecoveredOverlap
import EtaleFundamentalGroups.FiniteEtale.FiniteField.OverCoefficientCover
import EtaleFundamentalGroups.FiniteEtale.FiniteField.CommonCoverRecovery
import EtaleFundamentalGroups.FiniteEtale.FiniteField.OverCoverRecovery
import SchemeTheory.FiniteEtale.UniversalHomeomorphismFullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Gluing finite étale models across purely inseparable extensions
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace EtaleFundamentalGroups

export AlgebraicGeometry.Scheme.Cover
  (swappedPullbackCover
    gluingLocalOver
    gluingChartOver
    gluingLocalStructure
    gluingOverlapOver
    gluingOverlapFirst
    gluingOverlapSecond
    overPullback_product_isPullback
    recoveredPullbackOverlap_isPullback
    recoveredPullbackLocalModel
    recoveredPullbackLocalModelIso
    recoveredPullbackLocalIso
    recoveredPullbackChartMap
    recoveredPullbackChartCover
    recoveredPullbackChartMap_isOpenImmersion
    recoveredPullbackChartMap_isPullback
    recoveredPullbackChartMap_structure
    recoveredPullbackOverlapTransfer
    recoveredPullbackOverlapTransfer_structure
    recoveredPullbackOverlapTransfer_structure_assoc
    recoveredPullbackOverlapTransfer_chartMap
    recoveredPullbackOverlapTransfer_chartMap_assoc
    recoveredPullbackTransition
    recoveredPullbackTransition_first
    recoveredPullbackTransition_first_assoc
    recoveredPullbackTransition_chartMap)

variable {X Y : Scheme.{u}} (ψ : Y ⟶ X) (𝒰 : X.OpenCover)
variable (M : ∀ i : 𝒰.I₀, Over (𝒰.X i))
variable (Z : Over Y)
variable (e : ∀ i : 𝒰.I₀,
  (Over.pullback (pullback.fst (𝒰.f i) ψ)).obj (M i) ≅
    (Over.pullback (pullback.snd (𝒰.f i) ψ)).obj Z)

variable [hM : ∀ i : 𝒰.I₀, IsFiniteEtale (M i).hom]

instance gluingOverlapOver_etale (i j : 𝒰.I₀) : Etale (gluingOverlapOver 𝒰 M (i, j)).hom := by
  change Etale (pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f j) ≫ ((M i).hom ≫ 𝒰.f i))
  infer_instance

variable [IsIntegralHom ψ] [UniversallyInjective ψ] [Surjective ψ]

/-- The unique transition recovered by fully faithful radicial pullback. -/
def descendedGluingTransition (i j : 𝒰.I₀) :
    gluingOverlapOver 𝒰 M (i, j) ⟶ gluingOverlapOver 𝒰 M (j, i) :=
  (FiniteEtale.pullback_map_surjective_of_integral_universallyInjective_surjective ψ
    (gluingOverlapOver 𝒰 M (i, j)) (gluingOverlapOver 𝒰 M (j, i))
    (recoveredPullbackTransition ψ 𝒰 M Z e i j)).choose

theorem descendedGluingTransition_recovery (i j : 𝒰.I₀) :
    (Over.pullback ψ).map (descendedGluingTransition ψ 𝒰 M Z e i j) =
      recoveredPullbackTransition ψ 𝒰 M Z e i j :=
  (FiniteEtale.pullback_map_surjective_of_integral_universallyInjective_surjective ψ
    (gluingOverlapOver 𝒰 M (i, j)) (gluingOverlapOver 𝒰 M (j, i))
    (recoveredPullbackTransition ψ 𝒰 M Z e i j)).choose_spec

theorem descendedGluingTransition_structure (i j : 𝒰.I₀) :
    (descendedGluingTransition ψ 𝒰 M Z e i j).left ≫
      (gluingOverlapFirst 𝒰 M j i).left ≫ (M j).hom =
        pullback.snd ((M i).hom ≫ 𝒰.f i) (𝒰.f j) := by
  apply (cancel_mono (𝒰.f j)).mp
  simp only [Category.assoc]
  change (descendedGluingTransition ψ 𝒰 M Z e i j).left ≫
    (gluingOverlapOver 𝒰 M (j, i)).hom =
      pullback.snd ((M i).hom ≫ 𝒰.f i) (𝒰.f j) ≫ 𝒰.f j
  rw [Over.w]
  exact pullback.condition

theorem descendedGluingTransition_chartMap (i j : 𝒰.I₀) :
    ((Over.pullback ψ).map (descendedGluingTransition ψ 𝒰 M Z e i j)).left ≫
      ((Over.pullback ψ).map (gluingOverlapFirst 𝒰 M j i)).left ≫
        recoveredPullbackChartMap ψ 𝒰 M Z e j =
      ((Over.pullback ψ).map (gluingOverlapFirst 𝒰 M i j)).left ≫
        recoveredPullbackChartMap ψ 𝒰 M Z e i := by
  rw [descendedGluingTransition_recovery]
  exact recoveredPullbackTransition_chartMap ψ 𝒰 M Z e i j

local instance recoveredPullbackChartMap_mono (i : 𝒰.I₀) :
    Mono (recoveredPullbackChartMap ψ 𝒰 M Z e i) := by
  have := recoveredPullbackChartMap_isOpenImmersion ψ 𝒰 M Z e i
  infer_instance

/-- Recovery is injective on maps into each actual separated étale overlap. -/
private theorem gluingRecoveryFunctor_overlap_injective (T : Over X) (i j : 𝒰.I₀) :
    Function.Injective ((gluingRecoveryFunctor ψ).map
      (X := T) (Y := gluingOverlapOver 𝒰 M (i, j))) := by
  have : IsSeparated (gluingOverlapOver 𝒰 M (i, j)).hom := by
    change IsSeparated
      (pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f j) ≫ ((M i).hom ≫ 𝒰.f i))
    infer_instance
  intro a b hab
  apply (FiniteEtale.pullback_map_bijective_of_integral_universallyInjective_surjective
    ψ T (gluingOverlapOver 𝒰 M (i, j))).1
  exact Over.OverMorphism.ext hab

/-- Gluing data for the local models and their descended transitions. -/
def radicialLocalModelGlueData : Scheme.GlueData.{u} :=
  finiteStageGlueDataOfRecoveredTransitionsOfOverlapInjective 𝒰 (gluingLocalOver 𝒰 M)
    (gluingOverlapOver 𝒰 M) (gluingOverlapFirst 𝒰 M) (fun i => (M i).hom)
    (fun i j => pullback.snd ((M i).hom ≫ 𝒰.f i) (𝒰.f j))
    (fun i j => IsPullback.of_hasPullback ((M i).hom ≫ 𝒰.f i) (𝒰.f j))
    (descendedGluingTransition ψ 𝒰 M Z e) (descendedGluingTransition_structure ψ 𝒰 M Z e)
    ψ (recoveredPullbackChartMap ψ 𝒰 M Z e) (descendedGluingTransition_chartMap ψ 𝒰 M Z e)
    (gluingRecoveryFunctor_overlap_injective ψ 𝒰 M)

include hM in
theorem exists_finiteEtale_radicialLocalModelGlueData :
    ∃ q : (radicialLocalModelGlueData ψ 𝒰 M Z e).glued ⟶ X,
      IsFiniteEtale q ∧ ∀ i : 𝒰.I₀,
        IsPullback (M i).hom ((radicialLocalModelGlueData ψ 𝒰 M Z e).ι i) (𝒰.f i) q := by
  have : ∀ i : 𝒰.I₀,
      IsFiniteEtale (show (gluingLocalOver 𝒰 M i).left ⟶ 𝒰.X i from (M i).hom) := hM
  exact exists_finiteEtale_fromRecoveredTransitionsOfOverlapInjective 𝒰 (gluingLocalOver 𝒰 M)
    (gluingOverlapOver 𝒰 M) (gluingOverlapFirst 𝒰 M) (fun i => (M i).hom)
    (fun i j => pullback.snd ((M i).hom ≫ 𝒰.f i) (𝒰.f j))
    (fun i j => IsPullback.of_hasPullback ((M i).hom ≫ 𝒰.f i) (𝒰.f j))
    (descendedGluingTransition ψ 𝒰 M Z e) (descendedGluingTransition_structure ψ 𝒰 M Z e)
    ψ (recoveredPullbackChartMap ψ 𝒰 M Z e) (descendedGluingTransition_chartMap ψ 𝒰 M Z e)
    (gluingRecoveryFunctor_overlap_injective ψ 𝒰 M)

/-- The recovered raw overlap is the intersection of the two recovered charts. -/
theorem descendedGluingTransition_isPullback (i j : 𝒰.I₀) :
    IsPullback ((Over.pullback ψ).map (gluingOverlapFirst 𝒰 M i j)).left
      ((Over.pullback ψ).map
        (descendedGluingTransition ψ 𝒰 M Z e i j ≫ gluingOverlapFirst 𝒰 M j i)).left
      (recoveredPullbackChartMap ψ 𝒰 M Z e i)
      (recoveredPullbackChartMap ψ 𝒰 M Z e j) := by
  simp only [Functor.map_comp, Over.comp_left, descendedGluingTransition_recovery]
  refine isPullback_of_cartesian_chart_overlap
    (recoveredPullbackChartMap ψ 𝒰 M Z e i) (recoveredPullbackChartMap ψ 𝒰 M Z e j) Z.hom
    ((Over.pullback ψ).map (gluingLocalStructure 𝒰 M i)).left
    ((Over.pullback ψ).map (gluingLocalStructure 𝒰 M j)).left
    ((Over.pullback ψ).obj (gluingChartOver 𝒰 i)).hom
    ((Over.pullback ψ).obj (gluingChartOver 𝒰 j)).hom
    ((Over.pullback ψ).map (gluingOverlapFirst 𝒰 M i j)).left
    ((recoveredPullbackTransition ψ 𝒰 M Z e i j).left ≫
      ((Over.pullback ψ).map (gluingOverlapFirst 𝒰 M j i)).left)
    ((Over.pullback ψ).map (gluingOverlapSecond 𝒰 M i j)).left
    (recoveredPullbackChartMap_isPullback ψ 𝒰 M Z e i).w
    (recoveredPullbackChartMap_isPullback ψ 𝒰 M Z e j) ?_ ?_ ?_
  · rw [Over.w]
    exact recoveredPullbackOverlap_isPullback ψ 𝒰 M i j
  · rw [Category.assoc, recoveredPullbackTransition_first_assoc,
      recoveredPullbackOverlapTransfer_structure]
  · rw [Category.assoc]
    exact (recoveredPullbackTransition_chartMap ψ 𝒰 M Z e i j).symm

variable (q : (radicialLocalModelGlueData ψ 𝒰 M Z e).glued ⟶ X)
variable (hq : ∀ i : 𝒰.I₀,
  IsPullback (M i).hom ((radicialLocalModelGlueData ψ 𝒰 M Z e).ι i) (𝒰.f i) q)

/-- The inclusion of a local model into the glued relative scheme. -/
def radicialGluedChartInclusion (i : 𝒰.I₀) : gluingLocalOver 𝒰 M i ⟶ Over.mk q :=
  Over.homMk ((radicialLocalModelGlueData ψ 𝒰 M Z e).ι i) (hq i).w.symm

/-- The open cover of the glued scheme after coefficient pullback. -/
def radicialGluedPullbackCover : ((Over.pullback ψ).obj (Over.mk q)).left.OpenCover := by
  have : ∀ i : 𝒰.I₀, IsOpenImmersion (radicialGluedChartInclusion ψ 𝒰 M Z e q hq i).left :=
    fun i => (radicialLocalModelGlueData ψ 𝒰 M Z e).ι_isOpenImmersion i
  exact overCoefficientPullbackCover ψ (Over.mk q) (gluingLocalOver 𝒰 M)
    (radicialGluedChartInclusion ψ 𝒰 M Z e q hq)
    (radicialLocalModelGlueData ψ 𝒰 M Z e).ι_jointly_surjective

theorem radicialGluedPullbackCover_isPullback (i j : 𝒰.I₀) :
    IsPullback ((Over.pullback ψ).map (gluingOverlapFirst 𝒰 M i j)).left
      ((Over.pullback ψ).map
        (descendedGluingTransition ψ 𝒰 M Z e i j ≫ gluingOverlapFirst 𝒰 M j i)).left
      ((Over.pullback ψ).map (radicialGluedChartInclusion ψ 𝒰 M Z e q hq i)).left
      ((Over.pullback ψ).map (radicialGluedChartInclusion ψ 𝒰 M Z e q hq j)).left := by
  apply overCoefficientPullback_map_isPullback
  change IsPullback ((radicialLocalModelGlueData ψ 𝒰 M Z e).f i j)
    ((radicialLocalModelGlueData ψ 𝒰 M Z e).t i j ≫
      (radicialLocalModelGlueData ψ 𝒰 M Z e).f j i)
    ((radicialLocalModelGlueData ψ 𝒰 M Z e).ι i)
    ((radicialLocalModelGlueData ψ 𝒰 M Z e).ι j)
  exact IsPullback.of_isLimit ((radicialLocalModelGlueData ψ 𝒰 M Z e).vPullbackConeIsLimit i j)

include hq in
theorem nonempty_radicialGluedPullback_iso :
    Nonempty ((Over.pullback ψ).obj (Over.mk q) ≅ Z) := by
  let 𝒬 := radicialGluedPullbackCover ψ 𝒰 M Z e q hq
  let b : ∀ i : 𝒰.I₀, (Over.pullback ψ).obj (gluingLocalOver 𝒰 M i) ⟶ Z :=
    fun i => Over.homMk (recoveredPullbackChartMap ψ 𝒰 M Z e i)
      (recoveredPullbackChartMap_structure ψ 𝒰 M Z e i)
  have : ∀ i : 𝒰.I₀, IsOpenImmersion
      ((Over.pullback ψ).map (radicialGluedChartInclusion ψ 𝒰 M Z e q hq i)).left :=
    fun i => 𝒬.map_prop i
  have : ∀ i : 𝒰.I₀, IsOpenImmersion (b i).left :=
    fun i => recoveredPullbackChartMap_isOpenImmersion ψ 𝒰 M Z e i
  obtain ⟨eL, _⟩ := exists_over_iso_of_common_open_cover
    ((Over.pullback ψ).obj (Over.mk q)) Z
    (fun i : 𝒰.I₀ => (Over.pullback ψ).obj (gluingLocalOver 𝒰 M i))
    (fun ij : 𝒰.I₀ × 𝒰.I₀ => ((Over.pullback ψ).obj (gluingOverlapOver 𝒰 M ij)).left)
    (fun i j => ((Over.pullback ψ).map (gluingOverlapFirst 𝒰 M i j)).left)
    (fun i j => ((Over.pullback ψ).map
      (descendedGluingTransition ψ 𝒰 M Z e i j ≫ gluingOverlapFirst 𝒰 M j i)).left)
    (fun i => (Over.pullback ψ).map (radicialGluedChartInclusion ψ 𝒰 M Z e q hq i)) b
    𝒬.exists_eq (recoveredPullbackChartCover ψ 𝒰 M Z e).exists_eq
    (radicialGluedPullbackCover_isPullback ψ 𝒰 M Z e q hq)
    (descendedGluingTransition_isPullback ψ 𝒰 M Z e)
  exact ⟨eL⟩

include hM e in
/-- Actual finite étale local models with actual recovery glue to a global model
along a universal homeomorphism. -/
theorem exists_finiteEtale_model_of_local_models :
    ∃ N : FiniteEtale X,
      Nonempty ((Over.pullback ψ).obj ((FiniteEtale.forget X).obj N) ≅ Z) := by
  obtain ⟨q, hq, hc⟩ := exists_finiteEtale_radicialLocalModelGlueData ψ 𝒰 M Z e
  have : IsFiniteEtale q := hq
  exact ⟨FiniteEtale.mk q, nonempty_radicialGluedPullback_iso ψ 𝒰 M Z e q hc⟩

end EtaleFundamentalGroups
