/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ConstantFieldTower
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.FiniteFamilyModel
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ModelOverlap

/-!
# Constant Field Rebase

The standard iterated cover chart is the original chart after extending coefficients.
-/

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace EtaleFundamentalGroups

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
variable (F : IntermediateField k L) (X : Scheme.{u})
variable (f : X ⟶ Spec (CommRingCat.of k)) (𝒰 : X.OpenCover)
local notation "φF" => Spec.map (CommRingCat.ofHom (algebraMap k F))
local notation "φL" => Spec.map (CommRingCat.ofHom (algebraMap k L))
local notation "ψ" => Spec.map (CommRingCat.ofHom F.val.toRingHom)
local notation "UF" => constantFieldOpenCover k F X f 𝒰
local notation "UL" => constantFieldOpenCover k L X f 𝒰
local notation "UD" => constantFieldOpenCover F L (pullback φF f) (pullback.fst φF f) UF

/-- The standard iterated cover chart is the original chart after extending coefficients. -/
def constantFieldRebasedChartIso (i : 𝒰.I₀) :
    pullback ψ (coefficientModelMap φF f (𝒰.f i) ≫ pullback.fst φF f) ≅ pullback φL (𝒰.f i ≫ f) :=
  pullback.congrHom rfl (pullback.lift_fst _ _ _) ≪≫
    constantFieldTowerIso k L F (𝒰.X i) (𝒰.f i ≫ f)

theorem constantFieldRebasedChartIso_naturality (i : 𝒰.I₀) :
    (constantFieldRebasedChartIso k L F X f 𝒰 i).hom ≫ coefficientModelMap φL f (𝒰.f i) =
      coefficientModelMap ψ (pullback.fst φF f) (coefficientModelMap φF f (𝒰.f i)) ≫
        (constantFieldTowerIso k L F X f).hom := by
  apply pullback.hom_ext
  · simp only [constantFieldRebasedChartIso, Iso.trans_hom, Category.assoc,
      coefficientModelMap, pullback.lift_fst, constantFieldTowerIso_hom_fst,
      pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
  · simp only [constantFieldRebasedChartIso, Iso.trans_hom, Category.assoc,
      coefficientModelMap, pullback.lift_snd, constantFieldTowerIso_hom_snd]
    rw [reassoc_of% (constantFieldTowerIso_hom_snd k L F (𝒰.X i) (𝒰.f i ≫ f))]
    simp only [pullback.congrHom_hom, pullback.lift_snd_assoc, Category.id_comp,
      Category.assoc, pullback.lift_snd]

/-- Recovery of local finite étale models on the standard constant-field cover,
after changing the ground field to the common finite stage. -/
def constantFieldRebasedRecoveryIso (i : 𝒰.I₀)
    (M : FiniteEtale (pullback φF (𝒰.f i ≫ f)))
    (Z : FiniteEtale (pullback φL f))
    (e : (FiniteEtale.pullback
        (pullback.map φL (𝒰.f i ≫ f) φF (𝒰.f i ≫ f) ψ (𝟙 (𝒰.X i))
          (𝟙 (Spec (CommRingCat.of k)))
          (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
          (by rw [Category.comp_id, Category.id_comp]))).obj M ≅
      (FiniteEtale.pullback (coefficientModelMap φL f (𝒰.f i))).obj Z) :
    (FiniteEtale.pullback (pullback.snd ψ (coefficientModelMap φF f (𝒰.f i) ≫ pullback.fst φF
      f))).obj M ≅
      (FiniteEtale.pullback (coefficientModelMap ψ (pullback.fst φF f) (coefficientModelMap φF f
        (𝒰.f i)))).obj
        ((FiniteEtale.pullback (constantFieldTowerIso k L F X f).hom).obj Z) := by
  let eU := constantFieldRebasedChartIso k L F X f 𝒰 i
  let eX := constantFieldTowerIso k L F X f
  let cU : pullback φL (𝒰.f i ≫ f) ⟶ pullback φF (𝒰.f i ≫ f) :=
    pullback.map φL (𝒰.f i ≫ f) φF (𝒰.f i ≫ f) ψ (𝟙 (𝒰.X i))
      (𝟙 (Spec (CommRingCat.of k)))
      (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
      (by rw [Category.comp_id, Category.id_comp])
  have heU : eU.hom ≫ cU = pullback.snd ψ (coefficientModelMap φF f (𝒰.f i) ≫ pullback.fst φF f)
    := by
    change ((pullback.congrHom rfl (pullback.lift_fst _ _ _)).hom ≫
      (constantFieldTowerIso k L F (𝒰.X i) (𝒰.f i ≫ f)).hom) ≫ cU = _
    rw [Category.assoc, constantFieldTowerIso_hom_coefficientMap]
    exact pullback.lift_snd _ _ _
  have hnat : eU.hom ≫ coefficientModelMap φL f (𝒰.f i) = coefficientModelMap ψ (pullback.fst φF
    f) (coefficientModelMap φF f (𝒰.f i)) ≫ eX.hom :=
    constantFieldRebasedChartIso_naturality k L F X f 𝒰 i
  exact
    (FiniteEtale.finiteEtalePullbackCompObjIso eU.hom cU
      (pullback.snd ψ (coefficientModelMap φF f (𝒰.f i) ≫ pullback.fst φF f)) heU M).symm ≪≫
    (FiniteEtale.pullback eU.hom).mapIso e ≪≫
    FiniteEtale.finiteEtalePullbackCompObjIso eU.hom (coefficientModelMap φL f (𝒰.f i))
      (coefficientModelMap ψ (pullback.fst φF f) (coefficientModelMap φF f (𝒰.f i)) ≫ eX.hom) hnat
        Z ≪≫
    (FiniteEtale.finiteEtalePullbackCompObjIso (coefficientModelMap ψ (pullback.fst φF f)
      (coefficientModelMap φF f (𝒰.f i))) eX.hom
      (coefficientModelMap ψ (pullback.fst φF f) (coefficientModelMap φF f (𝒰.f i)) ≫ eX.hom) rfl
        Z).symm

end EtaleFundamentalGroups

namespace EtaleFundamentalGroups

/-- An actual finite étale cover over an algebraic extension supplies a common
finite coefficient field and recovered local models for the standard rebased cover. -/
theorem exists_finiteIntermediateField_rebased_local_models (k L : Type u) [Field k] [Field L]
  [Algebra k L] [Algebra.IsAlgebraic k L]
    (X : Scheme.{u}) [CompactSpace X] (f : X ⟶ Spec (CommRingCat.of k))
    (Z : FiniteEtale (pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)) :
    let 𝒰 := X.affineCover.finiteSubcover
    ∃ F : IntermediateField k L, FiniteDimensional k F ∧
      ∃ M : ∀ i : 𝒰.I₀, FiniteEtale
          (pullback (Spec.map (CommRingCat.ofHom (algebraMap k F))) (𝒰.f i ≫ f)),
        ∀ i : 𝒰.I₀, Nonempty ((FiniteEtale.pullback
          (pullback.snd (Spec.map (CommRingCat.ofHom F.val.toRingHom))
            (coefficientModelMap (Spec.map (CommRingCat.ofHom (algebraMap k F))) f (𝒰.f i) ≫
              pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k F))) f))).obj
              (M i) ≅
          (FiniteEtale.pullback (coefficientModelMap (Spec.map (CommRingCat.ofHom F.val.toRingHom))
            (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k F))) f)
            (coefficientModelMap (Spec.map (CommRingCat.ofHom (algebraMap k F))) f (𝒰.f i)))).obj
            ((FiniteEtale.pullback (constantFieldTowerIso k L F X f).hom).obj Z)) := by
  let 𝒰 := X.affineCover.finiteSubcover
  let : ∀ i : 𝒰.I₀, IsAffine (𝒰.X i) := fun i ↦ inferInstanceAs (IsAffine (Spec _))
  obtain ⟨F, hF, M, hrec⟩ :=
    FiniteEtale.exists_finiteIntermediateField_affine_scheme_model_family k L
      𝒰.X (fun i ↦ 𝒰.f i ≫ f)
      (fun i ↦ (FiniteEtale.pullback ((constantFieldOpenCover k L X f 𝒰).f i)).obj Z)
  refine ⟨F, hF, M, ?_⟩
  intro i
  exact ⟨constantFieldRebasedRecoveryIso k L F X f 𝒰 i (M i) Z (hrec i).some⟩

end EtaleFundamentalGroups
