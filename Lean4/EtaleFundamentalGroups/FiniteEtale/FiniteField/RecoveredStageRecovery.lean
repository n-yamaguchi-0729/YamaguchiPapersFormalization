/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import EtaleFundamentalGroups.FiniteEtale.FiniteField.RecoveredFiniteStage
import EtaleFundamentalGroups.FiniteEtale.FiniteField.RecoveredCoefficientRecovery
import EtaleFundamentalGroups.FiniteEtale.FiniteField.OverCoefficientCover
import EtaleFundamentalGroups.FiniteEtale.FiniteField.CommonCoverRecovery

/-!
# Recovered Stage Recovery

The actual recovered finite-stage charts form an open cover of the input scheme.
-/

noncomputable section
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
namespace EtaleFundamentalGroups
variable (k L : Type u) [Field k] [Field L] [Algebra k L]
variable (S : Scheme.{u}) (f : S ⟶ Spec (CommRingCat.of k)) (𝒰 : S.OpenCover)
variable (M : ∀ i : 𝒰.I₀, Over (𝒰.X i))
variable (Z : Over (pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f))
variable (e : ∀ i : 𝒰.I₀,
  (Over.pullback (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (𝒰.f i ≫ f))).obj (M i) ≅
      (Over.pullback ((constantFieldOpenCover k L S f 𝒰).f i)).obj Z)
variable (s : Finset L)

local notation "φL" => Spec.map (CommRingCat.ofHom (algebraMap k L))
local notation "E" => IntermediateField.adjoin k (s : Set L)
local notation "φE" => Spec.map (CommRingCat.ofHom
  (algebraMap k (IntermediateField.adjoin k (s : Set L))))
local notation "ψ" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (IntermediateField.val (IntermediateField.adjoin k (s : Set L)))))
local notation "𝒰E" => constantFieldOpenCover k (IntermediateField.adjoin k (s : Set L)) S f 𝒰
local notation "a" => (fun i : 𝒰.I₀ => Comma.hom (M i) ≫ 𝒰.f i)
local notation "V₀" => (fun ij : 𝒰.I₀ × 𝒰.I₀ =>
  pullback (Comma.hom (M (Prod.fst ij)) ≫ 𝒰.f (Prod.fst ij)) (𝒰.f (Prod.snd ij)))
local notation "p" => (fun ij : 𝒰.I₀ × 𝒰.I₀ =>
  pullback.fst (Comma.hom (M (Prod.fst ij)) ≫ 𝒰.f (Prod.fst ij)) (𝒰.f (Prod.snd ij)) ≫
    (Comma.hom (M (Prod.fst ij)) ≫ 𝒰.f (Prod.fst ij)))
local notation "AE" => (fun i : 𝒰.I₀ => coefficientLocalModelOver φE f (𝒰.f i) (Comma.hom (M i)))
local notation "VE" => (fun ij : 𝒰.I₀ × 𝒰.I₀ =>
  coefficientOverlapOver φE f (𝒰.f (Prod.fst ij)) (𝒰.f (Prod.snd ij)) (Comma.hom (M (Prod.fst ij))))
local notation "dE" => (fun i j : 𝒰.I₀ =>
  coefficientOverlapInclusion φE f (𝒰.f i) (𝒰.f j) (Comma.hom (M i)))
local notation "yE" => (fun i : 𝒰.I₀ =>
  coefficientLocalModelStructure φE f (𝒰.f i) (Comma.hom (M i)))
local notation "ℓE" => (fun i j : 𝒰.I₀ =>
  coefficientOverlapSecondMap φE f (𝒰.f i) (𝒰.f j) (Comma.hom (M i)))
local notation "hVE" => (fun i j : 𝒰.I₀ =>
  coefficientOverlap_isPullback φE f (𝒰.f i) (𝒰.f j) (Comma.hom (M i)))

variable (g : ∀ ij : 𝒰.I₀ × 𝒰.I₀, pullback (Spec.map (CommRingCat.ofHom (algebraMap k
  (IntermediateField.adjoin k (s : Set L))))) ((pullback.fst ((M ij.1).hom ≫ 𝒰.f ij.1) (𝒰.f ij.2)
  ≫ ((M ij.1).hom ≫ 𝒰.f ij.1)) ≫ f) ⟶
  pullback (Spec.map (CommRingCat.ofHom (algebraMap k (IntermediateField.adjoin k (s : Set L)))))
    ((pullback.fst ((M ij.2).hom ≫ 𝒰.f ij.2) (𝒰.f ij.1) ≫ ((M ij.2).hom ≫ 𝒰.f ij.2)) ≫ f))
variable (hgC : ∀ ij : 𝒰.I₀ × 𝒰.I₀,
  g ij ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k (IntermediateField.adjoin k (s :
    Set L))))) ((pullback.fst ((M ij.2).hom ≫ 𝒰.f ij.2) (𝒰.f ij.1) ≫ ((M ij.2).hom ≫ 𝒰.f ij.2)) ≫
    f) = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k (IntermediateField.adjoin k (s :
    Set L))))) ((pullback.fst ((M ij.1).hom ≫ 𝒰.f ij.1) (𝒰.f ij.2) ≫ ((M ij.1).hom ≫ 𝒰.f ij.1)) ≫
    f))
variable (hgS : ∀ ij : 𝒰.I₀ × 𝒰.I₀,
  g ij ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k (IntermediateField.adjoin k (s :
    Set L))))) ((pullback.fst ((M ij.2).hom ≫ 𝒰.f ij.2) (𝒰.f ij.1) ≫ ((M ij.2).hom ≫ 𝒰.f ij.2)) ≫
    f) ≫ (pullback.fst ((M ij.2).hom ≫ 𝒰.f ij.2) (𝒰.f ij.1) ≫ ((M ij.2).hom ≫ 𝒰.f ij.2)) =
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k (IntermediateField.adjoin k (s : Set
      L))))) ((pullback.fst ((M ij.1).hom ≫ 𝒰.f ij.1) (𝒰.f ij.2) ≫ ((M ij.1).hom ≫ 𝒰.f ij.1)) ≫ f)
      ≫ (pullback.fst ((M ij.1).hom ≫ 𝒰.f ij.1) (𝒰.f ij.2) ≫ ((M ij.1).hom ≫ 𝒰.f ij.1)))
variable (hgR : ∀ ij : 𝒰.I₀ × 𝒰.I₀,
  (constantFieldInverseLimitCone k L (pullback ((M ij.1).hom ≫ 𝒰.f ij.1) (𝒰.f ij.2))
    ((pullback.fst ((M ij.1).hom ≫ 𝒰.f ij.1) (𝒰.f ij.2) ≫ ((M ij.1).hom ≫ 𝒰.f ij.1)) ≫ f)).π.app
    (op s) ≫ g ij =
    recoveredCoefficientTransition k L S f 𝒰 M Z e ij.1 ij.2 ≫
      (constantFieldInverseLimitCone k L (pullback ((M ij.2).hom ≫ 𝒰.f ij.2) (𝒰.f ij.1))
        ((pullback.fst ((M ij.2).hom ≫ 𝒰.f ij.2) (𝒰.f ij.1) ≫ ((M ij.2).hom ≫ 𝒰.f ij.2)) ≫
        f)).π.app (op s))

/-- The actual recovered finite-stage charts form an open cover of the input scheme. -/
def recoveredStageChartCover : Z.left.OpenCover :=
  Scheme.Cover.copy (recoveredCoefficientChartCover k L S f 𝒰 M Z e) 𝒰.I₀
    (fun i => (gluingRecoveryFunctor ψ).obj (AE i))
    (recoveredStageChartMap k L S f 𝒰 M Z e s)
    (Equiv.refl _)
    (fun i => (constantFieldStagePullbackIso k L (M i).left (a i ≫ f) s).symm)
    (fun _ => rfl)

/-- The recovered finite-stage chart maps are open immersions. -/
theorem recoveredStageChartMap_isOpenImmersion (i : 𝒰.I₀) :
    IsOpenImmersion (recoveredStageChartMap k L S f 𝒰 M Z e s i) :=
  (recoveredStageChartCover k L S f 𝒰 M Z e s).map_prop i

include hgR in
/-- The actual pulled-back finite-stage overlaps are the intersections of the
recovered finite-stage charts in the input scheme. -/
theorem recoveredStageTransition_isPullback (i j : 𝒰.I₀) :
    IsPullback ((Over.pullback ψ).map (dE i j)).left
      ((Over.pullback ψ).map (recoveredStageTransition k L S f 𝒰 M s g hgC i j ≫ dE j i)).left
      (recoveredStageChartMap k L S f 𝒰 M Z e s i)
      (recoveredStageChartMap k L S f 𝒰 M Z e s j) := by
  have hd (m n : 𝒰.I₀) :
      (constantFieldStagePullbackIso k L (V₀ (m, n)) (p (m, n) ≫ f) s).hom ≫
        ((Over.pullback ψ).map (dE m n)).left =
      coefficientOverlapFirstMap φL f (𝒰.f m) (𝒰.f n) (M m).hom ≫
        (constantFieldStagePullbackIso k L (M m).left (a m ≫ f) s).hom :=
    constantFieldStagePullbackIso_naturality k L (V₀ (m, n)) (M m).left
      (p (m, n) ≫ f) (a m ≫ f) s
      (coefficientOverlapFirstMap φL f (𝒰.f m) (𝒰.f n) (M m).hom)
      (coefficientOverlapFirstMap φE f (𝒰.f m) (𝒰.f n) (M m).hom)
      (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _)
      (coefficientOverlapFirstMap_stage_naturality k L S (𝒰.X m) (𝒰.X n) (M m).left
        f (𝒰.f m) (𝒰.f n) (M m).hom s)
  have ht :
      (constantFieldStagePullbackIso k L (V₀ (i, j)) (p (i, j) ≫ f) s).hom ≫
        ((Over.pullback ψ).map (recoveredStageTransition k L S f 𝒰 M s g hgC i j)).left =
      recoveredCoefficientTransition k L S f 𝒰 M Z e i j ≫
        (constantFieldStagePullbackIso k L (V₀ (j, i)) (p (j, i) ≫ f) s).hom :=
    constantFieldStagePullbackIso_naturality k L (V₀ (i, j)) (V₀ (j, i))
      (p (i, j) ≫ f) (p (j, i) ≫ f) s
      (recoveredCoefficientTransition k L S f 𝒰 M Z e i j) (g (i, j))
      (recoveredCoefficientTransition_coefficient k L S f 𝒰 M Z e i j)
      (hgC (i, j)) (hgR (i, j))
  refine (recoveredCoefficientTransition_isPullback k L S f 𝒰 M Z e i j).of_iso
    (constantFieldStagePullbackIso k L (V₀ (i, j)) (p (i, j) ≫ f) s)
    (constantFieldStagePullbackIso k L (M i).left (a i ≫ f) s)
    (constantFieldStagePullbackIso k L (M j).left (a j ≫ f) s)
    (Iso.refl _) (hd i j).symm ?_ ?_ ?_
  · simp only [Functor.map_comp, Over.comp_left, Category.assoc]
    rw [← hd j i, ← reassoc_of% ht]
  · simp only [Iso.refl_hom, recoveredStageChartMap, Category.comp_id,
      Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, recoveredStageChartMap, Category.comp_id,
      Iso.hom_inv_id_assoc]

/-- The actual coefficient cone maps commute with the coefficient extension of
a map to the base scheme. -/
theorem coefficientModelMap_stage_naturality (Y : Scheme.{u}) (b : Y ⟶ S) :
    (constantFieldInverseLimitCone k L Y (b ≫ f)).π.app (op s) ≫
      coefficientModelMap φE f b =
    coefficientModelMap φL f b ≫ (constantFieldInverseLimitCone k L S f).π.app (op s) := by
  let rA : pullback φL (b ≫ f) ⟶ pullback φE (b ≫ f) :=
    (constantFieldInverseLimitCone k L Y (b ≫ f)).π.app (op s)
  let rS : pullback φL f ⟶ pullback φE f :=
    (constantFieldInverseLimitCone k L S f).π.app (op s)
  have hAf : rA ≫ pullback.fst φE (b ≫ f) = pullback.fst φL (b ≫ f) ≫ ψ :=
    constantFieldInverseLimitCone_π_app_fst k L Y (b ≫ f) s
  have hSf : rS ≫ pullback.fst φE f = pullback.fst φL f ≫ ψ :=
    constantFieldInverseLimitCone_π_app_fst k L S f s
  have hAs : rA ≫ pullback.snd φE (b ≫ f) = pullback.snd φL (b ≫ f) :=
    Over.w ((constantFieldInverseLimitOverCone k L Y (b ≫ f)).π.app (op s))
  have hSs : rS ≫ pullback.snd φE f = pullback.snd φL f :=
    Over.w ((constantFieldInverseLimitOverCone k L S f).π.app (op s))
  change rA ≫ coefficientModelMap φE f b = coefficientModelMap φL f b ≫ rS
  apply pullback.hom_ext
  · simp only [Category.assoc, coefficientModelMap, pullback.lift_fst]
    rw [hSf, pullback.lift_fst_assoc, hAf]
  · simp only [Category.assoc, coefficientModelMap, pullback.lift_snd]
    rw [hSs, pullback.lift_snd, reassoc_of% hAs]

/-- The original recovered coefficient chart has its actual map to the extended base. -/
theorem recoveredCoefficientChartMap_structure (i : 𝒰.I₀) :
    recoveredCoefficientChartMap k L S f 𝒰 M Z e i ≫ Z.hom =
      coefficientModelMap φL f (a i) := by
  have h : Scheme.Cover.recoveredLocalModelMap (constantFieldOpenCover k L S f 𝒰) Z
      (fun j => (Over.pullback (pullback.snd φL (𝒰.f j ≫ f))).obj (M j)) e i ≫ Z.hom =
      pullback.snd (M i).hom (pullback.snd φL (𝒰.f i ≫ f)) ≫
        coefficientModelMap φL f (𝒰.f i) :=
    Scheme.Cover.recoveredLocalModelMap_structure (constantFieldOpenCover k L S f 𝒰) Z
      (fun j => (Over.pullback (pullback.snd φL (𝒰.f j ≫ f))).obj (M j)) e i
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (modelTotalIso φL f (𝒰.f i) (M i).hom).inv ≫ z) h).trans
      (modelTotalIso_inv_coefficientModelMap φL f (𝒰.f i) (M i).hom))

variable (q : (recoveredFiniteStageGlueData k L S f 𝒰 M Z e s g hgC hgS hgR).glued ⟶
  pullback (Spec.map (CommRingCat.ofHom
    (algebraMap k (IntermediateField.adjoin k (s : Set L))))) f)
variable (hq : ∀ i : 𝒰.I₀,
  IsPullback (coefficientLocalModelStructure (Spec.map (CommRingCat.ofHom
    (algebraMap k (IntermediateField.adjoin k (s : Set L))))) f (𝒰.f i) (M i).hom)
    ((recoveredFiniteStageGlueData k L S f 𝒰 M Z e s g hgC hgS hgR).ι i)
    ((constantFieldOpenCover k (IntermediateField.adjoin k (s : Set L)) S f 𝒰).f i) q)

local notation "Dg" => recoveredFiniteStageGlueData k L S f 𝒰 M Z e s g hgC hgS hgR

/-- The chart inclusion of the actually glued scheme, retaining its coefficient structure. -/
def recoveredFiniteStageChartInclusion (i : 𝒰.I₀) :
    AE i ⟶ Over.mk (q ≫ pullback.fst φE f) := by
  let ιi : (AE i).left ⟶ (Dg).glued := (Dg).ι i
  have hbase : ιi ≫ q = coefficientModelMap φE f (a i) :=
    (hq i).w.symm.trans (coefficientLocalModelStructure_base φE f (𝒰.f i) (M i).hom)
  refine Over.homMk ιi ?_
  change ιi ≫ (q ≫ pullback.fst φE f) = pullback.fst φE (a i ≫ f)
  rw [← Category.assoc, hbase, pullback.lift_fst]

/-- The coefficient pullback of the actual glued model is covered by the
coefficient pullbacks of its original chart inclusions. -/
def recoveredFiniteStagePullbackCover :
    (pullback (q ≫ pullback.fst φE f) ψ).OpenCover := by
  have : ∀ i : 𝒰.I₀,
      IsOpenImmersion (recoveredFiniteStageChartInclusion k L S f 𝒰 M Z e s g hgC hgS hgR q hq
        i).left :=
    fun i => (Dg).ι_isOpenImmersion i
  exact overCoefficientPullbackCover ψ (Over.mk (q ≫ pullback.fst φE f)) (AE)
    (recoveredFiniteStageChartInclusion k L S f 𝒰 M Z e s g hgC hgS hgR q hq)
    (Dg).ι_jointly_surjective

/-- The coefficient-pulled-back gluing overlaps are the actual overlaps of the
coefficient-pulled-back glued model. -/
theorem recoveredFiniteStagePullbackCover_isPullback (i j : 𝒰.I₀) :
    IsPullback ((Over.pullback ψ).map (dE i j)).left
      ((Over.pullback ψ).map (recoveredStageTransition k L S f 𝒰 M s g hgC i j ≫ dE j i)).left
      ((Over.pullback ψ).map
        (recoveredFiniteStageChartInclusion k L S f 𝒰 M Z e s g hgC hgS hgR q hq i)).left
      ((Over.pullback ψ).map
        (recoveredFiniteStageChartInclusion k L S f 𝒰 M Z e s g hgC hgS hgR q hq j)).left := by
  apply overCoefficientPullback_map_isPullback
  change IsPullback ((Dg).f i j) ((Dg).t i j ≫ (Dg).f j i) ((Dg).ι i) ((Dg).ι j)
  exact IsPullback.of_isLimit ((Dg).vPullbackConeIsLimit i j)

/-- The coefficient extension of the actually glued finite-stage scheme recovers
the original scheme, with equality on every actual local chart. -/
theorem exists_recoveredFiniteStageGlueData_coefficient_iso :
    ∃ eL : pullback (q ≫ pullback.fst φE f) ψ ≅ Z.left,
      ∀ i : 𝒰.I₀,
        ((Over.pullback ψ).map
          (recoveredFiniteStageChartInclusion k L S f 𝒰 M Z e s g hgC hgS hgR q hq i)).left ≫
            eL.hom = recoveredStageChartMap k L S f 𝒰 M Z e s i := by
  let 𝒬 := recoveredFiniteStagePullbackCover k L S f 𝒰 M Z e s g hgC hgS hgR q hq
  have : ∀ i : 𝒰.I₀, IsOpenImmersion
      ((Over.pullback ψ).map
        (recoveredFiniteStageChartInclusion k L S f 𝒰 M Z e s g hgC hgS hgR q hq i)).left :=
    fun i => 𝒬.map_prop i
  have : ∀ i : 𝒰.I₀, IsOpenImmersion (recoveredStageChartMap k L S f 𝒰 M Z e s i) :=
    recoveredStageChartMap_isOpenImmersion k L S f 𝒰 M Z e s
  exact exists_iso_of_common_open_cover
    (pullback (q ≫ pullback.fst φE f) ψ) Z.left
    (fun i : 𝒰.I₀ => (gluingRecoveryFunctor ψ).obj (AE i))
    (fun ij : 𝒰.I₀ × 𝒰.I₀ => (gluingRecoveryFunctor ψ).obj (VE ij))
    (fun i j => ((Over.pullback ψ).map (dE i j)).left)
    (fun i j => ((Over.pullback ψ).map
      (recoveredStageTransition k L S f 𝒰 M s g hgC i j ≫ dE j i)).left)
    (fun i => ((Over.pullback ψ).map
      (recoveredFiniteStageChartInclusion k L S f 𝒰 M Z e s g hgC hgS hgR q hq i)).left)
    (recoveredStageChartMap k L S f 𝒰 M Z e s)
    𝒬.exists_eq (recoveredStageChartCover k L S f 𝒰 M Z e s).exists_eq
    (recoveredFiniteStagePullbackCover_isPullback k L S f 𝒰 M Z e s g hgC hgS hgR q hq)
    (recoveredStageTransition_isPullback k L S f 𝒰 M Z e s g hgC hgR)

/-- The coefficient pullback of the glued model has its actual structural map
to the original extended base. -/
def recoveredFiniteStageBaseMap : pullback (q ≫ pullback.fst φE f) ψ ⟶ pullback φL f :=
  (constantFieldInverseLimitCone_π_app_isPullback k L S f s).flip.lift
    (pullback.snd (q ≫ pullback.fst φE f) ψ)
    (pullback.fst (q ≫ pullback.fst φE f) ψ ≫ q)
    ((pullback.condition (f := q ≫ pullback.fst φE f) (g := ψ)).symm.trans
      (Category.assoc _ _ _).symm)

@[reassoc]
theorem recoveredFiniteStageBaseMap_stage :
    recoveredFiniteStageBaseMap k L S f 𝒰 M Z e s g hgC hgS hgR q ≫
      (constantFieldInverseLimitCone k L S f).π.app (op s) =
    pullback.fst (q ≫ pullback.fst φE f) ψ ≫ q :=
  (constantFieldInverseLimitCone_π_app_isPullback k L S f s).flip.lift_snd _ _ _

@[reassoc]
theorem recoveredFiniteStageBaseMap_coefficient :
    recoveredFiniteStageBaseMap k L S f 𝒰 M Z e s g hgC hgS hgR q ≫ pullback.fst φL f =
      pullback.snd (q ≫ pullback.fst φE f) ψ :=
  (constantFieldInverseLimitCone_π_app_isPullback k L S f s).flip.lift_fst _ _ _

/-- The coefficient pullback is also the actual pullback along the finite-stage
projection of the base scheme. -/
theorem recoveredFiniteStageBaseMap_isPullback :
    IsPullback (recoveredFiniteStageBaseMap k L S f 𝒰 M Z e s g hgC hgS hgR q)
      (pullback.fst (q ≫ pullback.fst φE f) ψ)
      ((constantFieldInverseLimitCone k L S f).π.app (op s)) q := by
  refine IsPullback.of_right ?_
    (recoveredFiniteStageBaseMap_stage k L S f 𝒰 M Z e s g hgC hgS hgR q)
    (constantFieldInverseLimitCone_π_app_isPullback k L S f s).flip
  rw [recoveredFiniteStageBaseMap_coefficient]
  exact (IsPullback.of_hasPullback (q ≫ pullback.fst φE f) ψ).flip

/-- Every recovered chart respects the actual base structural map of the
coefficient-pulled-back glued model. -/
theorem recoveredFiniteStageChartInclusion_baseMap (i : 𝒰.I₀) :
    ((Over.pullback ψ).map
      (recoveredFiniteStageChartInclusion k L S f 𝒰 M Z e s g hgC hgS hgR q hq i)).left ≫
        recoveredFiniteStageBaseMap k L S f 𝒰 M Z e s g hgC hgS hgR q =
      recoveredStageChartMap k L S f 𝒰 M Z e s i ≫ Z.hom := by
  let inc := recoveredFiniteStageChartInclusion k L S f 𝒰 M Z e s g hgC hgS hgR q hq i
  have hinc : inc.left ≫ q = coefficientModelMap φE f (a i) :=
    (hq i).w.symm.trans (coefficientLocalModelStructure_base φE f (𝒰.f i) (M i).hom)
  apply (cancel_epi (constantFieldStagePullbackIso k L (M i).left (a i ≫ f) s).hom).mp
  simp only [recoveredStageChartMap, Category.assoc, Iso.hom_inv_id_assoc,
    recoveredCoefficientChartMap_structure]
  let rS : pullback φL f ⟶ pullback φE f :=
    (constantFieldInverseLimitCone k L S f).π.app (op s)
  let bQ : pullback (q ≫ pullback.fst φE f) ψ ⟶ pullback φL f :=
    recoveredFiniteStageBaseMap k L S f 𝒰 M Z e s g hgC hgS hgR q
  have hQstage : bQ ≫ rS = pullback.fst (q ≫ pullback.fst φE f) ψ ≫ q :=
    recoveredFiniteStageBaseMap_stage k L S f 𝒰 M Z e s g hgC hgS hgR q
  have hQcoeff : bQ ≫ pullback.fst φL f = pullback.snd (q ≫ pullback.fst φE f) ψ :=
    recoveredFiniteStageBaseMap_coefficient k L S f 𝒰 M Z e s g hgC hgS hgR q
  have hS : IsPullback rS (pullback.fst φL f) (pullback.fst φE f) ψ :=
    constantFieldInverseLimitCone_π_app_isPullback k L S f s
  change (constantFieldStagePullbackIso k L (M i).left (a i ≫ f) s).hom ≫
    ((Over.pullback ψ).map inc).left ≫ bQ = coefficientModelMap φL f (a i)
  apply hS.hom_ext
  · simp only [Category.assoc, hQstage, Over.pullback_map_left, Over.mk_hom,
      pullback.lift_fst_assoc]
    rw [hinc, constantFieldStagePullbackIso_hom_fst_assoc]
    exact coefficientModelMap_stage_naturality k L S f s (M i).left (a i)
  · simp only [Category.assoc, hQcoeff, Over.pullback_map_left, Over.mk_hom,
      pullback.lift_snd]
    exact (constantFieldStagePullbackIso_hom_snd k L (M i).left (a i ≫ f) s).trans
      (pullback.lift_fst _ _ _).symm

include hq in
/-- The actual finite-stage glued scheme recovers the original object over the
extended base, not only its underlying scheme. -/
theorem nonempty_recoveredFiniteStageGlueData_over_iso :
    Nonempty ((Over.pullback ((constantFieldInverseLimitCone k L S f).π.app (op s))).obj
      (Over.mk q) ≅ Z) := by
  obtain ⟨eL, heL⟩ := exists_recoveredFiniteStageGlueData_coefficient_iso
    k L S f 𝒰 M Z e s g hgC hgS hgR q hq
  have hbase : eL.hom ≫ Z.hom =
      recoveredFiniteStageBaseMap k L S f 𝒰 M Z e s g hgC hgS hgR q := by
    apply (recoveredFiniteStagePullbackCover k L S f 𝒰 M Z e s g hgC hgS hgR q hq).hom_ext
    intro i
    change ((Over.pullback ψ).map
      (recoveredFiniteStageChartInclusion k L S f 𝒰 M Z e s g hgC hgS hgR q hq i)).left ≫
        (eL.hom ≫ Z.hom) = _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ Z.hom) (heL i)).trans
        (recoveredFiniteStageChartInclusion_baseMap k L S f 𝒰 M Z e s g hgC hgS hgR q hq i).symm)
  let hPB := recoveredFiniteStageBaseMap_isPullback k L S f 𝒰 M Z e s g hgC hgS hgR q
  refine ⟨Over.isoMk (hPB.flip.isoPullback.symm ≪≫ eL) ?_⟩
  change hPB.flip.isoPullback.inv ≫ eL.hom ≫ Z.hom = pullback.snd q _
  rw [hbase]
  exact hPB.flip.isoPullback_inv_snd

end EtaleFundamentalGroups
