/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import EtaleFundamentalGroups.FiniteEtale.FiniteField.OverlapTransitionDescent
import EtaleFundamentalGroups.FiniteEtale.FiniteField.RawStageGlue
import EtaleFundamentalGroups.FiniteEtale.FiniteField.RawOverlapSupplier
import EtaleFundamentalGroups.FiniteEtale.FiniteField.StageRecovery

/-!
# Recovered Finite Stage

The actually descended transition with its coefficient structure.
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

/-- The actually descended transition with its coefficient structure. -/
def recoveredStageTransition (i j : 𝒰.I₀) : VE (i, j) ⟶ VE (j, i) :=
  Over.homMk (g (i, j)) (hgC (i, j))

/-- The map from a recovered finite-stage chart to the original scheme. -/
def recoveredStageChartMap (i : 𝒰.I₀) :
    (gluingRecoveryFunctor ψ).obj (AE i) ⟶ Z.left :=
  (constantFieldStagePullbackIso k L (M i).left (a i ≫ f) s).inv ≫
    recoveredCoefficientChartMap k L S f 𝒰 M Z e i

/-- The recovered finite-stage chart map is a monomorphism. -/
theorem recoveredStageChartMap_mono (i : 𝒰.I₀) :
    Mono (recoveredStageChartMap k L S f 𝒰 M Z e s i) := by
  have : IsOpenImmersion (recoveredCoefficientChartMap k L S f 𝒰 M Z e i) :=
    recoveredCoefficientChartMap_isOpenImmersion k L S f 𝒰 M Z e i
  dsimp only [recoveredStageChartMap]
  infer_instance

include hgS in
/-- The descended transition respects the second actual base chart. -/
theorem recoveredStageTransition_structure (i j : 𝒰.I₀) :
    (recoveredStageTransition k L S f 𝒰 M s g hgC i j).left ≫
      (dE j i).left ≫ yE j = ℓE i j := by
  apply rawGluingTransition_structure (𝒰E) (AE) (VE) (dE) (yE) (ℓE) (hVE)
    (recoveredStageTransition k L S f 𝒰 M s g hgC) ?_ i j
  intro m n
  change g (m, n) ≫ (coefficientOverlapInclusion φE f (𝒰.f n) (𝒰.f m) (M n).hom).left ≫
      coefficientLocalModelStructure φE f (𝒰.f n) (M n).hom ≫ coefficientModelMap φE f (𝒰.f n) =
    (coefficientOverlapInclusion φE f (𝒰.f m) (𝒰.f n) (M m).hom).left ≫
      coefficientLocalModelStructure φE f (𝒰.f m) (M m).hom ≫ coefficientModelMap φE f (𝒰.f m)
  rw [coefficientOverlapInclusion_base, coefficientOverlapInclusion_base]
  apply pullback.hom_ext
  · simp only [Category.assoc, coefficientModelMap, pullback.lift_fst]
    exact hgC (m, n)
  · simp only [Category.assoc, coefficientModelMap, pullback.lift_snd]
    exact hgS (m, n)

include hgR in
/-- The descended transition recovers the original map to the given scheme. -/
theorem recoveredStageTransition_chartMap (i j : 𝒰.I₀) :
    (gluingRecoveryFunctor ψ).map (recoveredStageTransition k L S f 𝒰 M s g hgC i j) ≫
      (gluingRecoveryFunctor ψ).map (dE j i) ≫ recoveredStageChartMap k L S f 𝒰 M Z e s j =
    (gluingRecoveryFunctor ψ).map (dE i j) ≫ recoveredStageChartMap k L S f 𝒰 M Z e s i := by
  exact constantFieldStage_recovered_transition k L
    (M i).left (M j).left (V₀ (i, j)) (V₀ (j, i)) Z.left
    (a i ≫ f) (a j ≫ f) (p (i, j) ≫ f) (p (j, i) ≫ f) s
    (recoveredCoefficientTransition k L S f 𝒰 M Z e i j)
    (coefficientOverlapFirstMap φL f (𝒰.f j) (𝒰.f i) (M j).hom)
    (coefficientOverlapFirstMap φL f (𝒰.f i) (𝒰.f j) (M i).hom)
    (recoveredStageTransition k L S f 𝒰 M s g hgC i j) (dE j i) (dE i j)
    (recoveredCoefficientTransition_coefficient k L S f 𝒰 M Z e i j)
    (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) (hgR (i, j))
    (coefficientOverlapFirstMap_stage_naturality k L S (𝒰.X j) (𝒰.X i) (M j).left
      f (𝒰.f j) (𝒰.f i) (M j).hom s)
    (coefficientOverlapFirstMap_stage_naturality k L S (𝒰.X i) (𝒰.X j) (M i).left
      f (𝒰.f i) (𝒰.f j) (M i).hom s)
    (recoveredCoefficientChartMap k L S f 𝒰 M Z e i)
    (recoveredCoefficientChartMap k L S f 𝒰 M Z e j)
    (recoveredCoefficientTransition_chartMap k L S f 𝒰 M Z e i j)

/-- The actually descended finite family constructs finite-stage scheme gluing
data. No diagonal or cocycle laws are assumptions. -/
def recoveredFiniteStageGlueData : Scheme.GlueData.{u} := by
  have : Flat ψ := by
    rw [Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField _) _
  have : ∀ i : (𝒰E).I₀, Mono (recoveredStageChartMap k L S f 𝒰 M Z e s i) :=
    fun i => recoveredStageChartMap_mono k L S f 𝒰 M Z e s i
  exact finiteStageGlueDataOfRecoveredTransitions (𝒰E) (AE) (VE) (dE) (yE) (ℓE) (hVE)
    (recoveredStageTransition k L S f 𝒰 M s g hgC)
    (recoveredStageTransition_structure k L S f 𝒰 M s g hgC hgS)
    ψ (recoveredStageChartMap k L S f 𝒰 M Z e s)
    (recoveredStageTransition_chartMap k L S f 𝒰 M Z e s g hgC hgR)

/-- The actual finite-stage gluing data carry a finite étale structural map. -/
theorem recoveredFiniteStageGlueData_finiteEtale [∀ i : 𝒰.I₀, IsFiniteEtale (M i).hom] :
    ∃ q : (recoveredFiniteStageGlueData k L S f 𝒰 M Z e s g hgC hgS hgR).glued ⟶
        pullback φE f,
      IsFiniteEtale q ∧ ∀ i : 𝒰.I₀,
        IsPullback (yE i)
          ((recoveredFiniteStageGlueData k L S f 𝒰 M Z e s g hgC hgS hgR).ι i)
          ((𝒰E).f i) q := by
  have : Flat ψ := by
    rw [Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField _) _
  have : ∀ i : (𝒰E).I₀, Mono (recoveredStageChartMap k L S f 𝒰 M Z e s i) :=
    fun i => recoveredStageChartMap_mono k L S f 𝒰 M Z e s i
  have : ∀ i : (𝒰E).I₀,
      IsFiniteEtale (show (AE i).left ⟶ (𝒰E).X i from yE i) := by
    intro i
    have : IsFiniteEtale (M i).hom :=
      inferInstanceAs (IsFiniteEtale (M (show 𝒰.I₀ from i)).hom)
    exact coefficientLocalModelStructure_finiteEtale φE f (𝒰.f i) (M i).hom
  exact exists_finiteEtale_fromRecoveredTransitions (𝒰E) (AE) (VE) (dE) (yE) (ℓE) (hVE)
    (recoveredStageTransition k L S f 𝒰 M s g hgC)
    (recoveredStageTransition_structure k L S f 𝒰 M s g hgC hgS)
    ψ (recoveredStageChartMap k L S f 𝒰 M Z e s)
    (recoveredStageTransition_chartMap k L S f 𝒰 M Z e s g hgC hgR)

/-- The actual recovered finite family admits one finite coefficient stage with
actual gluing data and a finite étale glued scheme. The descended transitions
and their recovery equations are retained for global recovery. -/
theorem exists_finiteIntermediateField_recovered_glueData
    [Algebra.IsAlgebraic k L] [QuasiSeparatedSpace S]
    [Finite 𝒰.I₀] [∀ i : 𝒰.I₀, IsAffine (𝒰.X i)]
    [∀ i : 𝒰.I₀, IsFiniteEtale (M i).hom] :
    ∃ s₀ : Finset L, FiniteDimensional k (IntermediateField.adjoin k (s₀ : Set L)) ∧
      ∃ g₀ : ∀ ij : 𝒰.I₀ × 𝒰.I₀,
        pullback (Spec.map (CommRingCat.ofHom
          (algebraMap k (IntermediateField.adjoin k (s₀ : Set L))))) (p ij ≫ f) ⟶
        pullback (Spec.map (CommRingCat.ofHom
          (algebraMap k (IntermediateField.adjoin k (s₀ : Set L))))) (p (ij.2, ij.1) ≫ f),
      ∃ hg₀ : ∀ ij : 𝒰.I₀ × 𝒰.I₀,
        g₀ ij ≫ pullback.fst _ (p (ij.2, ij.1) ≫ f) = pullback.fst _ (p ij ≫ f) ∧
        g₀ ij ≫ pullback.snd _ (p (ij.2, ij.1) ≫ f) ≫ p (ij.2, ij.1) =
          pullback.snd _ (p ij ≫ f) ≫ p ij ∧
        (constantFieldInverseLimitCone k L (V₀ ij) (p ij ≫ f)).π.app (op s₀) ≫ g₀ ij =
          recoveredCoefficientTransition k L S f 𝒰 M Z e ij.1 ij.2 ≫
            (constantFieldInverseLimitCone k L (V₀ (ij.2, ij.1))
              (p (ij.2, ij.1) ≫ f)).π.app (op s₀),
      ∃ q : (recoveredFiniteStageGlueData k L S f 𝒰 M Z e s₀ g₀
          (fun ij => (hg₀ ij).1) (fun ij => (hg₀ ij).2.1) (fun ij => (hg₀ ij).2.2)).glued ⟶
        pullback (Spec.map (CommRingCat.ofHom
          (algebraMap k (IntermediateField.adjoin k (s₀ : Set L))))) f,
        IsFiniteEtale q ∧ ∀ i : 𝒰.I₀,
          IsPullback (coefficientLocalModelStructure (Spec.map (CommRingCat.ofHom
            (algebraMap k (IntermediateField.adjoin k (s₀ : Set L))))) f (𝒰.f i) (M i).hom)
            ((recoveredFiniteStageGlueData k L S f 𝒰 M Z e s₀ g₀
              (fun ij => (hg₀ ij).1) (fun ij => (hg₀ ij).2.1) (fun ij => (hg₀ ij).2.2)).ι i)
            ((constantFieldOpenCover k (IntermediateField.adjoin k (s₀ : Set L)) S f 𝒰).f i) q := by
  obtain ⟨s₀, hfin, g₀, hg₀⟩ :=
    exists_finiteIntermediateField_overlap_transitions k L S f 𝒰 M Z e
  refine ⟨s₀, hfin, g₀, hg₀, ?_⟩
  exact recoveredFiniteStageGlueData_finiteEtale k L S f 𝒰 M Z e s₀ g₀
    (fun ij => (hg₀ ij).1) (fun ij => (hg₀ ij).2.1) (fun ij => (hg₀ ij).2.2)

end EtaleFundamentalGroups
