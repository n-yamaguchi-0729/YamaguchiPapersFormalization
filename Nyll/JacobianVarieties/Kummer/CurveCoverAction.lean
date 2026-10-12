/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.CurveCover
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.RootScaling
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationSourceIso
import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
import Mathlib.AlgebraicGeometry.Normalization

/-!
# Root-of-unity automorphisms of the actual normalized Kummer cover

The explicit scaling automorphism of the generic root algebra extends through
the universal property of relative normalization. The construction uses the
original normalized finite étale cover, without assuming its connectedness.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory EtaleFundamentalGroups.Inertia
open JacobianVarieties.Kummer

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (n : ℕ+) (u : Pic0.kummerUnits K F n)

private def scalarRoot (ζ : rootsOfUnity (n : ℕ) K) :
    rootsOfUnity (n : ℕ) M.C.functionField :=
  restrictRootsOfUnity (baseToFunctionField M.toBase) (n : ℕ) ζ

/-- Scaling of the root in the original generic Kummer algebra, as an actual
isomorphism of its spectrum. -/
def kummerGenericRootScale (ζ : rootsOfUnity (n : ℕ) K) :
    Spec (.of (AdjoinRoot (Polynomial.X ^ (n : ℕ) -
        Polynomial.C (M.ffEquiv (u.val : F)) : Polynomial M.C.functionField))) ≅
      Spec (.of (AdjoinRoot (Polynomial.X ^ (n : ℕ) -
        Polynomial.C (M.ffEquiv (u.val : F)) : Polynomial M.C.functionField))) :=
  Scheme.Spec.mapIso (kummerRootScaleEquiv (n : ℕ) (M.ffEquiv (u.val : F))
    (scalarRoot M n ζ)).toRingEquiv.toCommRingCatIso.op

/-- Root scaling is over the original curve, since it fixes its function field. -/
theorem kummerGenericRootScale_hom_over (ζ : rootsOfUnity (n : ℕ) K) :
    (M.kummerGenericRootScale n u ζ).hom ≫ M.kummerGenericMap n u =
      M.kummerGenericMap n u := by
  let e := kummerRootScale (n : ℕ) (M.ffEquiv (u.val : F)) (scalarRoot M n ζ)
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField _)) ≫
        M.C.fromSpecStalk (genericPoint M.C)) = _
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact e.commutes a

private theorem kummerGenericRootScale_one :
    (M.kummerGenericRootScale n u 1).hom = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom
    (kummerRootScale (n : ℕ) (M.ffEquiv (u.val : F)) (scalarRoot M n 1)).toRingHom) = _
  have h : scalarRoot M n 1 = 1 := map_one _
  rw [h, kummerRootScale_one]
  exact Scheme.Spec.map_id _

private theorem kummerGenericRootScale_mul (ζ η : rootsOfUnity (n : ℕ) K) :
    (M.kummerGenericRootScale n u (ζ * η)).hom =
      (M.kummerGenericRootScale n u η).hom ≫ (M.kummerGenericRootScale n u ζ).hom := by
  change Spec.map (CommRingCat.ofHom
      (kummerRootScale (n : ℕ) (M.ffEquiv (u.val : F)) (scalarRoot M n (ζ * η))).toRingHom) =
    Spec.map (CommRingCat.ofHom
      (kummerRootScale (n : ℕ) (M.ffEquiv (u.val : F)) (scalarRoot M n η)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (kummerRootScale (n : ℕ) (M.ffEquiv (u.val : F)) (scalarRoot M n ζ)).toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  have h : scalarRoot M n (ζ * η) = scalarRoot M n η * scalarRoot M n ζ :=
    (map_mul (restrictRootsOfUnity (baseToFunctionField M.toBase) (n : ℕ)) ζ η).trans
      (mul_comm _ _)
  exact congrArg AlgHom.toRingHom
    ((congrArg (kummerRootScale (n : ℕ) (M.ffEquiv (u.val : F))) h).trans
      (kummerRootScale_mul (n : ℕ) (M.ffEquiv (u.val : F)) _ _))

/-- The generic root-scaling automorphism extends to the original relative
normalization through its proved universal property. -/
def kummerNormalizationRootScale (ζ : rootsOfUnity (n : ℕ) K) :
    (M.kummerGenericMap n u).normalization ≅ (M.kummerGenericMap n u).normalization :=
  normalizationSourceIso (M.kummerGenericMap n u) (M.kummerGenericMap n u)
    (M.kummerGenericRootScale n u ζ) (M.kummerGenericRootScale_hom_over n u ζ)

/-- The extension to normalization retains the original generic root scaling. -/
@[reassoc]
theorem toNormalization_kummerNormalizationRootScale (ζ : rootsOfUnity (n : ℕ) K) :
    (M.kummerGenericMap n u).toNormalization ≫ (M.kummerNormalizationRootScale n u ζ).hom =
      (M.kummerGenericRootScale n u ζ).hom ≫ (M.kummerGenericMap n u).toNormalization :=
  toNormalization_normalizationSourceIso_hom _ _ _ _

private theorem kummerNormalizationRootScale_over (ζ : rootsOfUnity (n : ℕ) K) :
    (M.kummerNormalizationRootScale n u ζ).hom ≫ (M.kummerGenericMap n u).fromNormalization =
      (M.kummerGenericMap n u).fromNormalization :=
  normalizationSourceIso_hom_fromNormalization _ _ _ _

private theorem kummerNormalizationRootScale_one :
    (M.kummerNormalizationRootScale n u 1).hom = 𝟙 _ := by
  apply Scheme.Hom.normalization.hom_ext (M.kummerGenericMap n u) _ _
    (M.kummerGenericMap n u).fromNormalization
  · rw [toNormalization_kummerNormalizationRootScale,
      kummerGenericRootScale_one, Category.id_comp, Category.comp_id]
  · exact kummerNormalizationRootScale_over M n u 1
  · exact Category.id_comp _

private theorem kummerNormalizationRootScale_mul (ζ η : rootsOfUnity (n : ℕ) K) :
    (M.kummerNormalizationRootScale n u (ζ * η)).hom =
      (M.kummerNormalizationRootScale n u η).hom ≫
        (M.kummerNormalizationRootScale n u ζ).hom := by
  apply Scheme.Hom.normalization.hom_ext (M.kummerGenericMap n u) _ _
    (M.kummerGenericMap n u).fromNormalization
  · rw [toNormalization_kummerNormalizationRootScale,
      toNormalization_kummerNormalizationRootScale_assoc,
      toNormalization_kummerNormalizationRootScale, kummerGenericRootScale_mul, Category.assoc]
  · exact kummerNormalizationRootScale_over M n u (ζ * η)
  · rw [Category.assoc, kummerNormalizationRootScale_over, kummerNormalizationRootScale_over]

/-- The extended automorphism is an automorphism of the actual finite étale
Kummer cover, including when the cover is disconnected. -/
def kummerCoverRootScale (hn : IsUnit ((n : ℕ) : K)) (ζ : rootsOfUnity (n : ℕ) K) :
    Aut (M.kummerCover n hn u) :=
  MorphismProperty.Over.isoMk (M.kummerNormalizationRootScale n u ζ)
    (normalizationSourceIso_hom_fromNormalization _ _ _ _)

/-- The actual roots of unity in the base field act by automorphisms of the
original normalized Kummer cover. -/
def kummerCoverRootScaleHom (hn : IsUnit ((n : ℕ) : K)) :
    rootsOfUnity (n : ℕ) K →* Aut (M.kummerCover n hn u) where
  toFun := M.kummerCoverRootScale n u hn
  map_one' := by
    apply Iso.ext
    apply MorphismProperty.Comma.Hom.ext'
    apply Over.OverMorphism.ext
    exact kummerNormalizationRootScale_one M n u
  map_mul' ζ η := by
    apply Iso.ext
    apply MorphismProperty.Comma.Hom.ext'
    apply Over.OverMorphism.ext
    exact kummerNormalizationRootScale_mul M n u ζ η

variable (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ M.C)

/-- The root-of-unity action on the actual geometric fiber, obtained from
the constructed automorphisms of the original Kummer cover. -/
@[instance_reducible]
def kummerGeometricRootAction :
    MulAction (rootsOfUnity (n : ℕ) K) ((FiniteEtale.fiber ξ).obj (M.kummerCover n hn u)) :=
  MulAction.compHom _ (M.kummerCoverRootScaleHom n u hn)

/-- Geometric monodromy commutes with root scaling, because every root
scaling is a morphism of the original finite étale cover. -/
theorem kummerGeometricRootAction_commutes :
    let := M.kummerGeometricRootAction n u hn ξ
    SMulCommClass (Aut (FiniteEtale.fiber ξ)) (rootsOfUnity (n : ℕ) K)
      ((FiniteEtale.fiber ξ).obj (M.kummerCover n hn u)) := by
  let := M.kummerGeometricRootAction n u hn ξ
  constructor
  intro g ζ x
  change g.hom.app (M.kummerCover n hn u)
      ((FiniteEtale.fiber ξ).map (M.kummerCoverRootScale n u hn ζ).hom x) =
    (FiniteEtale.fiber ξ).map (M.kummerCoverRootScale n u hn ζ).hom
      (g.hom.app (M.kummerCover n hn u) x)
  exact ConcreteCategory.congr_hom
    (g.hom.naturality (M.kummerCoverRootScale n u hn ζ).hom) x

end AlgebraicCurve.CurveModel
