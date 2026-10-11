/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.PureInseparableAffineDescent
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.FiniteFamilyModel
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ConstantFieldCover

/-!
# Pure Inseparable Cover Recovery

Recovery on a literal coefficient chart gives recovery on the standard
pullback chart, with both structure maps fixed.
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace EtaleFundamentalGroups

/-- Recovery on a literal coefficient chart gives recovery on the standard
pullback chart, with both structure maps fixed. -/
def constantFieldChartRecoveryIso
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (𝒰 : X.OpenCover) (i : 𝒰.I₀)
    (M : AlgebraicGeometry.FiniteEtale (𝒰.X i))
    (Z : AlgebraicGeometry.FiniteEtale
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f))
    (e : (AlgebraicGeometry.FiniteEtale.pullback
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) (𝒰.f i ≫ f))).obj M ≅
      (AlgebraicGeometry.FiniteEtale.pullback ((constantFieldOpenCover k L X f 𝒰).f i)).obj Z) :
    (AlgebraicGeometry.FiniteEtale.pullback
      (pullback.fst (𝒰.f i) (pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) f))).obj M ≅
      (AlgebraicGeometry.FiniteEtale.pullback
        (pullback.snd (𝒰.f i) (pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap k L))) f))).obj Z := by
  let φ : Spec (.of L) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let ψ : pullback φ f ⟶ X := pullback.snd φ f
  let u : 𝒰.X i ⟶ X := 𝒰.f i
  let uL : pullback φ (u ≫ f) ⟶ pullback φ f := (constantFieldOpenCover k L X f 𝒰).f i
  let c : pullback u ψ ≅ pullback φ (u ≫ f) :=
    pullbackSymmetry u ψ ≪≫ pullbackLeftPullbackSndIso φ f u
  have hfst : c.hom ≫ pullback.snd φ (u ≫ f) = pullback.fst u ψ := by
    dsimp only [c]
    rw [Iso.trans_hom, Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
      pullbackSymmetry_hom_comp_snd]
  have hcoeff : c.hom ≫ pullback.fst φ (u ≫ f) = pullback.snd u ψ ≫ pullback.fst φ f := by
    dsimp only [c]
    rw [Iso.trans_hom, Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
      ← Category.assoc, pullbackSymmetry_hom_comp_fst]
  have huLf : uL ≫ pullback.fst φ f = pullback.fst φ (u ≫ f) :=
    constantFieldOpenCover_f_fst k L X f 𝒰 i
  have huLs : uL ≫ pullback.snd φ f = pullback.snd φ (u ≫ f) ≫ u :=
    constantFieldOpenCover_f_snd k L X f 𝒰 i
  have hsnd : c.hom ≫ uL = pullback.snd u ψ := by
    apply pullback.hom_ext
    · rw [Category.assoc, huLf]
      exact hcoeff
    · rw [Category.assoc, huLs,
        ← Category.assoc, hfst]
      exact pullback.condition
  exact (AlgebraicGeometry.FiniteEtale.finiteEtalePullbackCompObjIso c.hom
    (pullback.snd φ (u ≫ f)) (pullback.fst u ψ) hfst M).symm ≪≫
      (AlgebraicGeometry.FiniteEtale.pullback c.hom).mapIso e ≪≫
        AlgebraicGeometry.FiniteEtale.finiteEtalePullbackCompObjIso c.hom uL
          (pullback.snd u ψ) hsnd Z

/-- An affine open cover supplies actual local models and their standard
pullback-chart recoveries over a purely inseparable extension. -/
theorem exists_purelyInseparable_affineCover_models
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsPurelyInseparable k L]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (𝒰 : X.OpenCover)
    [∀ i : 𝒰.I₀, IsAffine (𝒰.X i)]
    (Z : AlgebraicGeometry.FiniteEtale
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)) :
    ∃ M : ∀ i : 𝒰.I₀, AlgebraicGeometry.FiniteEtale (𝒰.X i),
      ∀ i : 𝒰.I₀, Nonempty
        ((Over.pullback (pullback.fst (𝒰.f i) (pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap k L))) f))).obj
            ((AlgebraicGeometry.FiniteEtale.forget (𝒰.X i)).obj (M i)) ≅
          (Over.pullback (pullback.snd (𝒰.f i) (pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap k L))) f))).obj
              ((AlgebraicGeometry.FiniteEtale.forget _).obj Z)) := by
  classical
  let ZL (i : 𝒰.I₀) :=
    (AlgebraicGeometry.FiniteEtale.pullback ((constantFieldOpenCover k L X f 𝒰).f i)).obj Z
  have hmodels (i : 𝒰.I₀) :=
    exists_affine_model_of_purelyInseparable_extension k L (𝒰.X i) (𝒰.f i ≫ f) (ZL i)
  choose M hM using hmodels
  refine ⟨M, fun i ↦ ⟨?_⟩⟩
  exact (AlgebraicGeometry.FiniteEtale.forget _).mapIso
    (constantFieldChartRecoveryIso k L X f 𝒰 i (M i) Z (hM i).some)

end EtaleFundamentalGroups
