/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Open covers after constant-field extension

The constant-field base change of an open cover retains its index type and literal pullback
charts. Its chart inclusions preserve both projections, and affine charts remain affine.
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u v
namespace EtaleFundamentalGroups
variable (k E : Type u) [Field k] [Field E] [Algebra k E]

/-- Base change of an open cover, with chart objects the literal constant-field
base changes of the original charts and the same index type. -/
def constantFieldOpenCover (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    (𝒰 : Scheme.OpenCover.{v} X) :
    Scheme.OpenCover.{v} (pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) f) := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k E))
  refine Scheme.Cover.copy (𝒰.pullback₁ (pullback.snd φ f)) 𝒰.I₀
    (fun i ↦ pullback φ (𝒰.f i ≫ f))
    (fun i ↦ pullback.lift (pullback.fst φ (𝒰.f i ≫ f))
      (pullback.snd φ (𝒰.f i ≫ f) ≫ 𝒰.f i) (by
        rw [Category.assoc]
        exact pullback.condition))
    (Equiv.refl _) (fun i ↦ (pullbackLeftPullbackSndIso φ f (𝒰.f i)).symm) ?_
  intro i
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc]
    exact (pullbackLeftPullbackSndIso_inv_fst φ f (𝒰.f i)).symm
  · rw [pullback.lift_snd, Category.assoc]
    exact (pullbackLeftPullbackSndIso_inv_fst_snd φ f (𝒰.f i)).symm

/-- The literal chart inclusion preserves the coefficient projection. -/
theorem constantFieldOpenCover_f_fst (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (𝒰 : Scheme.OpenCover.{v} X) (i : 𝒰.I₀) :
    (constantFieldOpenCover k E X f 𝒰).f i ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) f =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) (𝒰.f i ≫ f) := by
  exact pullback.lift_fst _ _ _

/-- The literal chart inclusion lies over the original chart inclusion. -/
theorem constantFieldOpenCover_f_snd (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (𝒰 : Scheme.OpenCover.{v} X) (i : 𝒰.I₀) :
    (constantFieldOpenCover k E X f 𝒰).f i ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k E))) f =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k E))) (𝒰.f i ≫ f) ≫ 𝒰.f i := by
  exact pullback.lift_snd _ _ _

/-- Affine charts stay affine under the literal constant-field cover construction. -/
theorem constantFieldOpenCover_isAffine (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (𝒰 : Scheme.OpenCover.{v} X)
    (i : 𝒰.I₀) [IsAffine (𝒰.X i)] :
    IsAffine ((constantFieldOpenCover k E X f 𝒰).X i) := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let : IsAffineHom (pullback.snd φ (𝒰.f i ≫ f)) :=
    MorphismProperty.pullback_snd
      (P := (show MorphismProperty Scheme.{u} from @IsAffineHom)) φ (𝒰.f i ≫ f) inferInstance
  change IsAffine (pullback φ (𝒰.f i ≫ f))
  exact isAffine_of_isAffineHom (Y := 𝒰.X i) (pullback.snd φ (𝒰.f i ≫ f))

end EtaleFundamentalGroups
