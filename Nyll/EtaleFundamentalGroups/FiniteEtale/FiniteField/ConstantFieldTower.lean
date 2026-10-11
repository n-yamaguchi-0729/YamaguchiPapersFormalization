/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.FieldTheory.IntermediateField.Basic
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ConstantFieldCover
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.FiniteFamilyModel

/-!
# Constant Field Tower

Rebase a constant extension through an actual intermediate field.
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u v
namespace EtaleFundamentalGroups
variable (k L : Type u) [Field k] [Field L] [Algebra k L]
variable (F : IntermediateField k L)

local notation "φF" => Spec.map (CommRingCat.ofHom (algebraMap k F))
local notation "φL" => Spec.map (CommRingCat.ofHom (algebraMap k L))
local notation "ψ" => Spec.map (CommRingCat.ofHom F.val.toRingHom)

private theorem coefficientSpec_comp : ψ ≫ φF = φL := by
  rw [← Spec.map_comp]
  rfl

variable (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))

local notation "c" =>
  pullback.map φL f φF f ψ (𝟙 X) (𝟙 (Spec (CommRingCat.of k)))
    (Eq.trans (Category.comp_id φL) (Eq.symm (coefficientSpec_comp k L F)))
    (Eq.trans (Category.comp_id f) (Eq.symm (Category.id_comp f)))

/-- Rebase a constant extension through an actual intermediate field. -/
def constantFieldTowerIso : pullback ψ (pullback.fst φF f) ≅ pullback φL f :=
  pullbackRightPullbackFstIso φF f ψ ≪≫
    pullback.congrHom (coefficientSpec_comp k L F) rfl

/-- The tower comparison preserves the coefficient coordinate. -/
theorem constantFieldTowerIso_hom_fst :
    (constantFieldTowerIso k L F X f).hom ≫ pullback.fst φL f =
      pullback.fst ψ (pullback.fst φF f) := by
  simp only [constantFieldTowerIso, Iso.trans_hom, pullback.congrHom_hom,
    Category.assoc, pullback.lift_fst, Category.comp_id, pullbackRightPullbackFstIso_hom_fst]

/-- The tower comparison preserves the underlying original-scheme coordinate. -/
theorem constantFieldTowerIso_hom_snd :
    (constantFieldTowerIso k L F X f).hom ≫ pullback.snd φL f =
      pullback.snd ψ (pullback.fst φF f) ≫ pullback.snd φF f := by
  simp only [constantFieldTowerIso, Iso.trans_hom, pullback.congrHom_hom,
    Category.assoc, pullback.lift_snd, Category.comp_id, pullbackRightPullbackFstIso_hom_snd]

/-- The iterated base-change projection is the literal coefficient inclusion. -/
theorem constantFieldTowerIso_hom_coefficientMap :
    (constantFieldTowerIso k L F X f).hom ≫ c = pullback.snd ψ (pullback.fst φF f) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    rw [← Category.assoc, constantFieldTowerIso_hom_fst]
    exact pullback.condition
  · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
    exact constantFieldTowerIso_hom_snd k L F X f

/-- The inverse comparison also identifies the two projection maps. -/
theorem constantFieldTowerIso_inv_snd :
    (constantFieldTowerIso k L F X f).inv ≫ pullback.snd ψ (pullback.fst φF f) = c := by
  rw [← constantFieldTowerIso_hom_coefficientMap k L F X f, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- The chart map after rebasing the native constant-field cover through `F`. -/
def constantFieldTowerCoverMap (𝒰 : Scheme.OpenCover.{v} X) (i : 𝒰.I₀) :
    pullback ψ (pullback.fst φF (𝒰.f i ≫ f)) ⟶ pullback ψ (pullback.fst φF f) := by
  let uF : pullback φF (𝒰.f i ≫ f) ⟶ pullback φF f :=
    (constantFieldOpenCover k F X f 𝒰).f i
  have huF : uF ≫ pullback.fst φF f = pullback.fst φF (𝒰.f i ≫ f) :=
    constantFieldOpenCover_f_fst k F X f 𝒰 i
  exact pullback.lift (pullback.fst ψ (pullback.fst φF (𝒰.f i ≫ f)))
    (pullback.snd ψ (pullback.fst φF (𝒰.f i ≫ f)) ≫ uF)
    (by rw [Category.assoc, huF]; exact pullback.condition)
/-- The tower comparisons commute with the actual constant-field chart inclusions. -/
theorem constantFieldTowerIso_cover_naturality (𝒰 : Scheme.OpenCover.{v} X) (i : 𝒰.I₀) :
    constantFieldTowerCoverMap k L F X f 𝒰 i ≫ (constantFieldTowerIso k L F X f).hom =
      (constantFieldTowerIso k L F (𝒰.X i) (𝒰.f i ≫ f)).hom ≫
        (constantFieldOpenCover k L X f 𝒰).f i := by
  let uF : pullback φF (𝒰.f i ≫ f) ⟶ pullback φF f :=
    (constantFieldOpenCover k F X f 𝒰).f i
  let uL : pullback φL (𝒰.f i ≫ f) ⟶ pullback φL f :=
    (constantFieldOpenCover k L X f 𝒰).f i
  let uD : pullback ψ (pullback.fst φF (𝒰.f i ≫ f)) ⟶ pullback ψ (pullback.fst φF f) :=
    constantFieldTowerCoverMap k L F X f 𝒰 i
  have hFsnd : uF ≫ pullback.snd φF f = pullback.snd φF (𝒰.f i ≫ f) ≫ 𝒰.f i :=
    constantFieldOpenCover_f_snd k F X f 𝒰 i
  have hLfst : uL ≫ pullback.fst φL f = pullback.fst φL (𝒰.f i ≫ f) :=
    constantFieldOpenCover_f_fst k L X f 𝒰 i
  have hLsnd : uL ≫ pullback.snd φL f = pullback.snd φL (𝒰.f i ≫ f) ≫ 𝒰.f i :=
    constantFieldOpenCover_f_snd k L X f 𝒰 i
  have hDfst : uD ≫ pullback.fst ψ (pullback.fst φF f) =
      pullback.fst ψ (pullback.fst φF (𝒰.f i ≫ f)) := pullback.lift_fst _ _ _
  have hDsnd : uD ≫ pullback.snd ψ (pullback.fst φF f) =
      pullback.snd ψ (pullback.fst φF (𝒰.f i ≫ f)) ≫ uF := pullback.lift_snd _ _ _
  change uD ≫ (constantFieldTowerIso k L F X f).hom =
    (constantFieldTowerIso k L F (𝒰.X i) (𝒰.f i ≫ f)).hom ≫ uL
  apply pullback.hom_ext
  · rw [Category.assoc, constantFieldTowerIso_hom_fst, hDfst, Category.assoc,
      hLfst, constantFieldTowerIso_hom_fst]
  · rw [Category.assoc, constantFieldTowerIso_hom_snd, ← Category.assoc, hDsnd,
      Category.assoc, hFsnd, Category.assoc, hLsnd, ← Category.assoc,
      ← Category.assoc, constantFieldTowerIso_hom_snd]
/-- The rebased charts form an actual open cover of the iterated constant extension. -/
def constantFieldTowerOpenCover (𝒰 : Scheme.OpenCover.{v} X) :
    Scheme.OpenCover.{v} (pullback ψ (pullback.fst φF f)) := by
  let eX : pullback ψ (pullback.fst φF f) ≅ pullback φL f :=
    constantFieldTowerIso k L F X f
  let 𝒰L : Scheme.OpenCover.{v} (pullback φL f) := constantFieldOpenCover k L X f 𝒰
  have h (i : 𝒰.I₀) : IsPullback (constantFieldTowerCoverMap k L F X f 𝒰 i)
      (constantFieldTowerIso k L F (𝒰.X i) (𝒰.f i ≫ f)).hom eX.hom (𝒰L.f i) :=
    IsPullback.of_vert_isIso ⟨constantFieldTowerIso_cover_naturality k L F X f 𝒰 i⟩
  refine Scheme.Cover.copy (𝒰L.pullback₁ eX.hom) 𝒰.I₀
    (fun i ↦ pullback ψ (pullback.fst φF (𝒰.f i ≫ f)))
    (constantFieldTowerCoverMap k L F X f 𝒰) (Equiv.refl _)
    (fun i ↦ (h i).isoPullback) ?_
  intro i
  exact (h i).isoPullback_hom_fst.symm
/-- Transport an actual local-model recovery isomorphism to the rebased field. -/
def constantFieldTowerRecoveryIso (𝒰 : Scheme.OpenCover.{v} X) (i : 𝒰.I₀)
    (M : AlgebraicGeometry.FiniteEtale (pullback φF (𝒰.f i ≫ f)))
    (Z : AlgebraicGeometry.FiniteEtale (pullback φL f))
    (e : (AlgebraicGeometry.FiniteEtale.pullback
        (pullback.map φL (𝒰.f i ≫ f) φF (𝒰.f i ≫ f) ψ (𝟙 (𝒰.X i))
          (𝟙 (Spec (CommRingCat.of k)))
          (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
          (by rw [Category.comp_id, Category.id_comp]))).obj M ≅
      (AlgebraicGeometry.FiniteEtale.pullback
        ((constantFieldOpenCover k L X f 𝒰).f i)).obj Z) :
    (AlgebraicGeometry.FiniteEtale.pullback
        (pullback.snd ψ (pullback.fst φF (𝒰.f i ≫ f)))).obj M ≅
      (AlgebraicGeometry.FiniteEtale.pullback
        (constantFieldTowerCoverMap k L F X f 𝒰 i)).obj
          ((AlgebraicGeometry.FiniteEtale.pullback (constantFieldTowerIso k L F X f).hom).obj Z)
            := by
  let eU : pullback ψ (pullback.fst φF (𝒰.f i ≫ f)) ≅ pullback φL (𝒰.f i ≫ f) :=
    constantFieldTowerIso k L F (𝒰.X i) (𝒰.f i ≫ f)
  let eX : pullback ψ (pullback.fst φF f) ≅ pullback φL f :=
    constantFieldTowerIso k L F X f
  let cU : pullback φL (𝒰.f i ≫ f) ⟶ pullback φF (𝒰.f i ≫ f) :=
    pullback.map φL (𝒰.f i ≫ f) φF (𝒰.f i ≫ f) ψ (𝟙 (𝒰.X i))
      (𝟙 (Spec (CommRingCat.of k)))
      (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
      (by rw [Category.comp_id, Category.id_comp])
  let uL : pullback φL (𝒰.f i ≫ f) ⟶ pullback φL f :=
    (constantFieldOpenCover k L X f 𝒰).f i
  let uD : pullback ψ (pullback.fst φF (𝒰.f i ≫ f)) ⟶ pullback ψ (pullback.fst φF f) :=
    constantFieldTowerCoverMap k L F X f 𝒰 i
  have heU : eU.hom ≫ cU = pullback.snd ψ (pullback.fst φF (𝒰.f i ≫ f)) :=
    constantFieldTowerIso_hom_coefficientMap k L F (𝒰.X i) (𝒰.f i ≫ f)
  have hnat : uD ≫ eX.hom = eU.hom ≫ uL :=
    constantFieldTowerIso_cover_naturality k L F X f 𝒰 i
  exact
    (AlgebraicGeometry.FiniteEtale.finiteEtalePullbackCompObjIso eU.hom cU
      (pullback.snd ψ (pullback.fst φF (𝒰.f i ≫ f))) heU M).symm ≪≫
    (AlgebraicGeometry.FiniteEtale.pullback eU.hom).mapIso e ≪≫
    AlgebraicGeometry.FiniteEtale.finiteEtalePullbackCompObjIso eU.hom uL
      (uD ≫ eX.hom) hnat.symm Z ≪≫
    (AlgebraicGeometry.FiniteEtale.finiteEtalePullbackCompObjIso uD eX.hom
      (uD ≫ eX.hom) rfl Z).symm
end EtaleFundamentalGroups
