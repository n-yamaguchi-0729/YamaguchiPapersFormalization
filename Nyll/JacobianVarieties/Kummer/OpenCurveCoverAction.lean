/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.OpenCurveCover
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

open AlgebraicGeometry CategoryTheory EtaleFundamentalGroups.Inertia TopologicalSpace
open JacobianVarieties.Kummer

namespace AlgebraicCurve.CurveModel.OpenKummer

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
  (a : Pic0.openKummerUnits K F S n)
  {U : Scheme.{u}} [IsIntegral U] (j : U ⟶ M.C) [IsOpenImmersion j]
  (hj : DenseRange j)

private def scalarRoot (ζ : rootsOfUnity (n : ℕ) K) :
    rootsOfUnity (n : ℕ) U.functionField :=
  restrictRootsOfUnity (baseToFunctionField (j ≫ M.toBase)) (n : ℕ) ζ

/-- Scaling of the root in the original generic Kummer algebra, as an actual
isomorphism of its spectrum. -/
def kummerGenericRootScale (ζ : rootsOfUnity (n : ℕ) K) :
    Spec (.of (AdjoinRoot (Polynomial.X ^ (n : ℕ) -
        Polynomial.C (j.functionFieldMap hj (M.ffEquiv (a.val : F))) : Polynomial
            U.functionField))) ≅
      Spec (.of (AdjoinRoot (Polynomial.X ^ (n : ℕ) -
        Polynomial.C (j.functionFieldMap hj (M.ffEquiv (a.val : F))) : Polynomial
            U.functionField))) :=
  Scheme.Spec.mapIso (kummerRootScaleEquiv (n : ℕ) (j.functionFieldMap hj (M.ffEquiv (a.val :
      F)))
    (scalarRoot M n j ζ)).toRingEquiv.toCommRingCatIso.op

omit [IsOpenImmersion j] in
/-- Root scaling is over the original curve, since it fixes its function field. -/
theorem kummerGenericRootScale_hom_over (ζ : rootsOfUnity (n : ℕ) K) :
    (kummerGenericRootScale M S n a j hj ζ).hom ≫ M.openKummerGenericMap S n a j hj =
      M.openKummerGenericMap S n a j hj := by
  let e := kummerRootScale (n : ℕ) (j.functionFieldMap hj (M.ffEquiv (a.val : F))) (scalarRoot
      M n j ζ)
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap U.functionField _)) ≫
        U.fromSpecStalk (genericPoint U)) = _
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact e.commutes a

omit [IsOpenImmersion j] in
private theorem kummerGenericRootScale_one :
    (kummerGenericRootScale M S n a j hj 1).hom = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom
    (kummerRootScale (n : ℕ) (j.functionFieldMap hj (M.ffEquiv (a.val : F))) (scalarRoot M n j
        1)).toRingHom) = _
  have h : scalarRoot M n j 1 = 1 := map_one _
  rw [h, kummerRootScale_one]
  exact Scheme.Spec.map_id _

omit [IsOpenImmersion j] in
private theorem kummerGenericRootScale_mul (ζ η : rootsOfUnity (n : ℕ) K) :
    (kummerGenericRootScale M S n a j hj (ζ * η)).hom =
      (kummerGenericRootScale M S n a j hj η).hom ≫ (kummerGenericRootScale M S n a j hj ζ).hom
          := by
  change Spec.map (CommRingCat.ofHom
      (kummerRootScale (n : ℕ) (j.functionFieldMap hj (M.ffEquiv (a.val : F))) (scalarRoot M n
          j (ζ * η))).toRingHom) =
    Spec.map (CommRingCat.ofHom
      (kummerRootScale (n : ℕ) (j.functionFieldMap hj (M.ffEquiv (a.val : F))) (scalarRoot M n
          j η)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (kummerRootScale (n : ℕ) (j.functionFieldMap hj (M.ffEquiv (a.val : F))) (scalarRoot M n
          j ζ)).toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  have h : scalarRoot M n j (ζ * η) = scalarRoot M n j η * scalarRoot M n j ζ :=
    (map_mul (restrictRootsOfUnity (baseToFunctionField (j ≫ M.toBase)) (n : ℕ)) ζ η).trans
      (mul_comm _ _)
  exact congrArg AlgHom.toRingHom
    ((congrArg (kummerRootScale (n : ℕ) (j.functionFieldMap hj (M.ffEquiv (a.val : F))))
        h).trans
      (kummerRootScale_mul (n : ℕ) (j.functionFieldMap hj (M.ffEquiv (a.val : F))) _ _))

/-- The generic root-scaling automorphism extends to the original relative
normalization through its proved universal property. -/
def kummerNormalizationRootScale (ζ : rootsOfUnity (n : ℕ) K) :
    (M.openKummerGenericMap S n a j hj).normalization ≅ (M.openKummerGenericMap S n a j
        hj).normalization :=
  normalizationSourceIso (M.openKummerGenericMap S n a j hj) (M.openKummerGenericMap S n a j
      hj)
    (kummerGenericRootScale M S n a j hj ζ) (kummerGenericRootScale_hom_over M S n a j hj ζ)

omit [IsOpenImmersion j] in
/-- The extension to normalization retains the original generic root scaling. -/
@[reassoc]
theorem toNormalization_kummerNormalizationRootScale (ζ : rootsOfUnity (n : ℕ) K) :
    (M.openKummerGenericMap S n a j hj).toNormalization ≫ (kummerNormalizationRootScale M S n a
        j hj ζ).hom =
      (kummerGenericRootScale M S n a j hj ζ).hom ≫ (M.openKummerGenericMap S n a j
          hj).toNormalization :=
  toNormalization_normalizationSourceIso_hom _ _ _ _

omit [IsOpenImmersion j] in
private theorem kummerNormalizationRootScale_over (ζ : rootsOfUnity (n : ℕ) K) :
    (kummerNormalizationRootScale M S n a j hj ζ).hom ≫ (M.openKummerGenericMap S n a j
        hj).fromNormalization =
      (M.openKummerGenericMap S n a j hj).fromNormalization :=
  normalizationSourceIso_hom_fromNormalization _ _ _ _

omit [IsOpenImmersion j] in
private theorem kummerNormalizationRootScale_one :
    (kummerNormalizationRootScale M S n a j hj 1).hom = 𝟙 _ := by
  apply Scheme.Hom.normalization.hom_ext (M.openKummerGenericMap S n a j hj) _ _
    (M.openKummerGenericMap S n a j hj).fromNormalization
  · rw [toNormalization_kummerNormalizationRootScale,
      kummerGenericRootScale_one, Category.id_comp, Category.comp_id]
  · exact kummerNormalizationRootScale_over M S n a j hj 1
  · exact Category.id_comp _

omit [IsOpenImmersion j] in
private theorem kummerNormalizationRootScale_mul (ζ η : rootsOfUnity (n : ℕ) K) :
    (kummerNormalizationRootScale M S n a j hj (ζ * η)).hom =
      (kummerNormalizationRootScale M S n a j hj η).hom ≫
        (kummerNormalizationRootScale M S n a j hj ζ).hom := by
  apply Scheme.Hom.normalization.hom_ext (M.openKummerGenericMap S n a j hj) _ _
    (M.openKummerGenericMap S n a j hj).fromNormalization
  · rw [toNormalization_kummerNormalizationRootScale,
      toNormalization_kummerNormalizationRootScale_assoc,
      toNormalization_kummerNormalizationRootScale, kummerGenericRootScale_mul, Category.assoc]
  · exact kummerNormalizationRootScale_over M S n a j hj (ζ * η)
  · rw [Category.assoc, kummerNormalizationRootScale_over, kummerNormalizationRootScale_over]

variable [CompactSpace U]
  (hinterior : ∀ (y : U) (x : closedPoints M.C),
    x.val = j y → M.placeOfPoint x ∉ S)

/-- The extended automorphism is an automorphism of the actual finite étale
Kummer cover, including when the cover is disconnected. -/
def kummerCoverRootScale (hn : IsUnit ((n : ℕ) : K)) (ζ : rootsOfUnity (n : ℕ) K) :
    Aut (M.openKummerCover S n hn a j hj hinterior) :=
  MorphismProperty.Over.isoMk (kummerNormalizationRootScale M S n a j hj ζ)
    (normalizationSourceIso_hom_fromNormalization _ _ _ _)

/-- The actual roots of unity in the base field act by automorphisms of the
original normalized Kummer cover. -/
def kummerCoverRootScaleHom (hn : IsUnit ((n : ℕ) : K)) :
    rootsOfUnity (n : ℕ) K →* Aut (M.openKummerCover S n hn a j hj hinterior) where
  toFun := kummerCoverRootScale M S n a j hj hinterior hn
  map_one' := by
    apply Iso.ext
    apply MorphismProperty.Comma.Hom.ext'
    apply Over.OverMorphism.ext
    exact kummerNormalizationRootScale_one M S n a j hj
  map_mul' ζ η := by
    apply Iso.ext
    apply MorphismProperty.Comma.Hom.ext'
    apply Over.OverMorphism.ext
    exact kummerNormalizationRootScale_mul M S n a j hj ζ η

variable (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ U)

/-- The root-of-unity action on the actual geometric fiber, obtained from
the constructed automorphisms of the original Kummer cover. -/
@[instance_reducible]
def kummerGeometricRootAction :
    MulAction (rootsOfUnity (n : ℕ) K) ((FiniteEtale.fiber ξ).obj (M.openKummerCover S n hn a j
        hj hinterior)) :=
  MulAction.compHom _ (kummerCoverRootScaleHom M S n a j hj hinterior hn)

/-- Geometric monodromy commutes with root scaling, because every root
scaling is a morphism of the original finite étale cover. -/
theorem kummerGeometricRootAction_commutes :
    let := kummerGeometricRootAction M S n a j hj hinterior hn ξ
    SMulCommClass (Aut (FiniteEtale.fiber ξ)) (rootsOfUnity (n : ℕ) K)
      ((FiniteEtale.fiber ξ).obj (M.openKummerCover S n hn a j hj hinterior)) := by
  let := kummerGeometricRootAction M S n a j hj hinterior hn ξ
  constructor
  intro g ζ x
  change g.hom.app (M.openKummerCover S n hn a j hj hinterior)
      ((FiniteEtale.fiber ξ).map (kummerCoverRootScale M S n a j hj hinterior hn ζ).hom x) =
    (FiniteEtale.fiber ξ).map (kummerCoverRootScale M S n a j hj hinterior hn ζ).hom
      (g.hom.app (M.openKummerCover S n hn a j hj hinterior) x)
  exact ConcreteCategory.congr_hom
    (g.hom.naturality (kummerCoverRootScale M S n a j hj hinterior hn ζ).hom) x

end AlgebraicCurve.CurveModel.OpenKummer
