/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import EtaleFundamentalGroups.FiniteEtale.FiniteField.AffineSchemeModel
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Finite Family Model

The canonical finite étale comparison for two successive pullbacks,
with the composite map and category explicitly fixed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.FiniteEtale

private def coefficientBaseChangeMap
    (k A B : Type u) [Field k] [Field A] [Field B] [Algebra k A] [Algebra k B]
    (U : Scheme.{u}) (f : U ⟶ Spec (CommRingCat.of k)) (v : A →ₐ[k] B) :
    Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k B))) f ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f :=
  Limits.pullback.map _ _ _ _ (Spec.map (CommRingCat.ofHom v.toRingHom))
    (𝟙 U) (𝟙 (Spec (CommRingCat.of k)))
    (by
      rw [Category.comp_id, ← Spec.map_comp]
      apply congrArg Spec.map
      ext x
      exact (v.commutes x).symm)
    (by rw [Category.comp_id, Category.id_comp])

private theorem coefficientBaseChangeMap_comp
    (k A B C : Type u) [Field k] [Field A] [Field B] [Field C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (U : Scheme.{u}) (f : U ⟶ Spec (CommRingCat.of k))
    (v : A →ₐ[k] B) (w : B →ₐ[k] C) :
    coefficientBaseChangeMap k B C U f w ≫ coefficientBaseChangeMap k A B U f v =
      coefficientBaseChangeMap k A C U f (w.comp v) := by
  apply Limits.pullback.hom_ext
  · simp only [coefficientBaseChangeMap, Limits.pullback.map, Category.assoc,
      Limits.pullback.lift_fst]
    rw [← Category.assoc, Limits.pullback.lift_fst, Category.assoc, ← Spec.map_comp]
    rfl
  · simp only [coefficientBaseChangeMap, Limits.pullback.map, Category.assoc,
      Limits.pullback.lift_snd, Category.comp_id]

/-- The canonical finite étale comparison for two successive pullbacks,
with the composite map and category explicitly fixed. -/
def finiteEtalePullbackCompObjIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : f ≫ g = fg) (A : AlgebraicGeometry.FiniteEtale Z) :
    (AlgebraicGeometry.FiniteEtale.pullback f).obj
      ((AlgebraicGeometry.FiniteEtale.pullback g).obj A) ≅
        (AlgebraicGeometry.FiniteEtale.pullback fg).obj A := by
  let : MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
    ⟨fun h hf ↦ MorphismProperty.of_isPullback
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) g :=
    ⟨fun h hf ↦ MorphismProperty.of_isPullback
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩
  let : MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
  let : MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) g := ⟨fun _ _ ↦ inferInstance⟩
  let e : AlgebraicGeometry.FiniteEtale.pullback fg ≅
      AlgebraicGeometry.FiniteEtale.pullback g ⋙ AlgebraicGeometry.FiniteEtale.pullback f :=
    MorphismProperty.Over.pullbackComp (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
      (Q := ⊤) f g fg hfg.symm
  exact (e.app A).symm

/-- A finite family of finite étale covers of affine constant extensions has
actual models over one common finite intermediate field. -/
theorem exists_finiteIntermediateField_affine_scheme_model_family
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    {ι : Type u} [Finite ι] (U : ι → Scheme.{u}) [∀ i, IsAffine (U i)]
    (f : ∀ i, U i ⟶ Spec (CommRingCat.of k))
    (X : ∀ i, AlgebraicGeometry.FiniteEtale
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) (f i))) :
    ∃ F : IntermediateField k L, FiniteDimensional k F ∧
      ∃ X₀ : ∀ i, AlgebraicGeometry.FiniteEtale
        (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k F))) (f i)),
        ∀ i, Nonempty ((AlgebraicGeometry.FiniteEtale.pullback
          (Limits.pullback.map (Spec.map (CommRingCat.ofHom (algebraMap k L))) (f i)
            (Spec.map (CommRingCat.ofHom (algebraMap k F))) (f i)
            (Spec.map (CommRingCat.ofHom F.val.toRingHom)) (𝟙 (U i))
            (𝟙 (Spec (CommRingCat.of k)))
            (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
            (by rw [Category.id_comp, Category.comp_id]))).obj (X₀ i) ≅ X i) := by
  classical
  choose Fᵢ hFᵢ Mᵢ eᵢ using fun i ↦
    exists_finiteIntermediateField_affine_scheme_model k L (U i) (f i) (X i)
  let : ∀ i, FiniteDimensional k (Fᵢ i) := hFᵢ
  let F : IntermediateField k L := ⨆ i, Fᵢ i
  let v (i : ι) : Fᵢ i →ₐ[k] F := IntermediateField.inclusion (le_iSup Fᵢ i)
  let a (i : ι) := coefficientBaseChangeMap k (Fᵢ i) F (U i) (f i) (v i)
  let b (i : ι) := coefficientBaseChangeMap k F L (U i) (f i) F.val
  let c (i : ι) := coefficientBaseChangeMap k (Fᵢ i) L (U i) (f i) (Fᵢ i).val
  have hcomp (i : ι) : b i ≫ a i = c i := by
    dsimp only [a, b, c]
    rw [coefficientBaseChangeMap_comp]
    rfl
  let M (i : ι) : AlgebraicGeometry.FiniteEtale
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k F))) (f i)) :=
    (AlgebraicGeometry.FiniteEtale.pullback (a i)).obj (Mᵢ i)
  refine ⟨F, inferInstance, M, ?_⟩
  intro i
  change Nonempty ((AlgebraicGeometry.FiniteEtale.pullback (b i)).obj (M i) ≅ X i)
  exact ⟨finiteEtalePullbackCompObjIso (b i) (a i) (c i) (hcomp i) (Mᵢ i) ≪≫
    (eᵢ i).some⟩

end AlgebraicGeometry.FiniteEtale
