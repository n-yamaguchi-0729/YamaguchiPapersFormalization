/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.OpenCurveCoverCharacter
import Nyll.JacobianVarieties.Kummer.OpenCurveCoverTorsor
import Nyll.JacobianVarieties.Kummer.OpenCurveCoverAction
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldMonodromyLift
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.RootScaling
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.RootFiberTransitivity
import Nyll.EtaleFundamentalGroups.Cohomology.TorsorCharacter
import Mathlib.RingTheory.AdjoinRoot

/-!
# The actual Kummer character at the geometric generic point

A chosen root defines a point of the original generic root algebra and hence
of its relative normalization. Root scaling and actual Galois monodromy send
that point to the same point precisely at the usual root quotient. The proved
free action then computes the character as the factor carrying β to σ β.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory TopologicalSpace
open JacobianVarieties.Kummer EtaleFundamentalGroups.Cohomology
open scoped FintypeCatDiscrete

namespace AlgebraicCurve.CurveModel.OpenKummer

attribute [local instance] IsSepClosure.sep_closed

variable {K : Type u} [Field K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
  (w : Pic0.openKummerUnits K F S n)
  {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hinterior : ∀ (y : X) (x : closedPoints M.C),
    x.val = j y → M.placeOfPoint x ∉ S)
  {Ω : Type u} [Field Ω] [Algebra X.functionField Ω]
  (β : Ω) (hβ : β ^ (n : ℕ) = algebraMap X.functionField Ω (j.functionFieldMap hj (M.ffEquiv
    (w.val : F))))

private def genericKummerRootLift :
    AdjoinRoot (Polynomial.X ^ (n : ℕ) -
      Polynomial.C (j.functionFieldMap hj (M.ffEquiv (w.val : F))) : Polynomial
        X.functionField) →ₐ[X.functionField]
        Ω :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId X.functionField Ω) β (by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    exact sub_eq_zero.mpr hβ)

omit [CompactSpace X] [IsOpenImmersion j] in
private theorem genericKummerRootLift_root :
    genericKummerRootLift M S n w j hj β hβ (AdjoinRoot.root _) = β :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

private def genericKummerRootPoint :
    Spec (.of Ω) ⟶ (M.openKummerGenericMap S n w j hj).normalization :=
  Spec.map (CommRingCat.ofHom (genericKummerRootLift M S n w j hj β hβ).toRingHom) ≫
    (M.openKummerGenericMap S n w j hj).toNormalization

omit [CompactSpace X] [IsOpenImmersion j] in
private theorem genericKummerRootPoint_over :
    genericKummerRootPoint M S n w j hj β hβ ≫ (M.openKummerGenericMap S n w j
      hj).fromNormalization =
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X) := by
  rw [genericKummerRootPoint, Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
  change Spec.map (CommRingCat.ofHom (genericKummerRootLift M S n w j hj β hβ).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap X.functionField _)) ≫
      X.fromSpecStalk (genericPoint X)) = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hmap : (genericKummerRootLift M S n w j hj β hβ).toRingHom.comp
      (algebraMap X.functionField _) = algebraMap X.functionField Ω := by
    apply RingHom.ext
    intro a
    exact (genericKummerRootLift M S n w j hj β hβ).commutes a
  exact congrArg (fun φ : X.functionField →+* Ω =>
    Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X)) hmap

omit [CompactSpace X] [IsOpenImmersion j] in
private theorem genericKummerRootPoint_scale
    (ζ : rootsOfUnity (n : ℕ) K) (σ : Ω ≃ₐ[X.functionField] Ω)
    (hscale : algebraMap X.functionField Ω
      (baseToFunctionField (j ≫ M.toBase) ((ζ : Kˣ) : K)) * β = σ β) :
    genericKummerRootPoint M S n w j hj β hβ ≫ (kummerNormalizationRootScale M S n w j hj ζ).hom =
      Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ genericKummerRootPoint M S n w j hj β hβ := by
  let a := j.functionFieldMap hj (M.ffEquiv (w.val : F))
  let η : rootsOfUnity (n : ℕ) X.functionField :=
    restrictRootsOfUnity (baseToFunctionField (j ≫ M.toBase)) (n : ℕ) ζ
  let l := genericKummerRootLift M S n w j hj β hβ
  have halg : l.comp (kummerRootScale (n : ℕ) a η) = σ.toAlgHom.comp l := by
    apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, kummerRootScale_root, map_mul, AlgHom.commutes,
      genericKummerRootLift_root, AlgHom.comp_apply, genericKummerRootLift_root]
    exact hscale
  have hring := congrArg AlgHom.toRingHom halg
  change l.toRingHom.comp (kummerRootScale (n : ℕ) a η).toRingHom =
    (σ : Ω →+* Ω).comp l.toRingHom at hring
  rw [genericKummerRootPoint, Category.assoc,
    AlgebraicCurve.CurveModel.OpenKummer.toNormalization_kummerNormalizationRootScale]
  rw [← Category.assoc, ← Category.assoc]
  apply congrArg (· ≫ (M.openKummerGenericMap S n w j hj).toNormalization)
  change Spec.map (CommRingCat.ofHom l.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (kummerRootScale (n : ℕ) a η).toRingHom) = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, hring]

variable [IsSepClosed K]

include hβ

/-- At the actual geometric generic point, the Kummer monodromy character
multiplies a chosen root β by exactly the factor that sends β to σ β. -/
theorem kummerMonodromyCharacter_generic_mul_root
    [IsSepClosure X.functionField Ω] (hn : IsUnit ((n : ℕ) : K))
    (σ : Ω ≃ₐ[X.functionField] Ω) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let xi := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let genericMap := X.fromSpecStalk (genericPoint X)
    let g := FiniteEtale.fundamentalGroupHom genericMap xi
      (toAut (FiniteEtale.fiber xi) (Ω ≃ₐ[X.functionField] Ω) σ)
    algebraMap X.functionField Ω (baseToFunctionField (j ≫ M.toBase)
      ((kummerMonodromyCharacter M S n w j hj hinterior hn (xi ≫ genericMap) g : Kˣ) : K)) * β
        = σ β := by
  intro tμ xi genericMap g
  let T := kummerGeometricRootTorsor M S n w j hj hinterior hn (xi ≫ genericMap)
  have := kummerGeometricRootAction_commutes M S n w j hj hinterior hn (xi ≫ genericMap)
  let ι : K →+* Ω := (algebraMap X.functionField Ω).comp (baseToFunctionField (j ≫ M.toBase))
  have hβ0 : β ≠ 0 := by
    intro hz
    have hzero : algebraMap X.functionField Ω (j.functionFieldMap hj (M.ffEquiv (w.val : F)))
      = 0 := by
      rw [← hβ, hz, zero_pow n.ne_zero]
    have hzero' : j.functionFieldMap hj (M.ffEquiv (w.val : F)) = 0 :=
      (algebraMap X.functionField Ω).injective
        (hzero.trans (map_zero (algebraMap X.functionField Ω)).symm)
    have hzero'' : M.ffEquiv (w.val : F) = 0 :=
      (j.functionFieldMap hj).injective
        (hzero'.trans (map_zero (j.functionFieldMap hj)).symm)
    exact (Units.ne_zero w.val) (M.ffEquiv.injective
      (hzero''.trans (map_zero M.ffEquiv).symm))
  have hpow : β ^ (n : ℕ) = (σ β) ^ (n : ℕ) := by
    rw [← map_pow, hβ, AlgEquiv.commutes]
  obtain ⟨ζ, hζ, _⟩ := EtaleFundamentalGroups.Kummer.existsUnique_rootScale
    ι n hn β (σ β) hβ0 hpow
  let W := M.openKummerCover S n hn w j hj hinterior
  let s := genericKummerRootPoint M S n w j hj β hβ
  let e := FiniteEtale.fiberObjEquivHom (xi ≫ genericMap) W
  let x : (FiniteEtale.fiber (xi ≫ genericMap)).obj W :=
    e.symm (Over.homMk s (genericKummerRootPoint_over M S n w j hj β hβ))
  have hx : (e x).left = s := congrArg (fun q => q.left) (e.apply_symm_apply _)
  have hζx : ζ • x = g • x := by
    apply e.injective
    apply Over.OverMorphism.ext
    have hleft := congrArg (fun q => q.left)
      (FiniteEtale.fiberObjEquivHom_naturality (xi ≫ genericMap)
        (kummerCoverRootScale M S n w j hj hinterior hn ζ).hom x)
    have hright := FiniteEtale.fundamentalGroupHom_field_fiberLift genericMap W σ x
    change (e x).left ≫ (kummerNormalizationRootScale M S n w j hj ζ).hom =
      (e (ζ • x)).left at hleft
    change (e (g • x)).left = Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
      (e x).left at hright
    exact hleft.symm.trans ((congrArg (· ≫ (kummerNormalizationRootScale M S n w j hj ζ).hom)
      hx).trans
      ((genericKummerRootPoint_scale M S n w j hj β hβ ζ σ hζ).trans
        ((congrArg (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ ·) hx.symm).trans
          hright.symm)))
  have hχx : kummerMonodromyCharacter M S n w j hj hinterior hn (xi ≫ genericMap) g • x = g •
    x := by
    rw [kummerMonodromyCharacter_eq_torsorCharacter M S n w j hj hinterior hn (xi ≫ genericMap) x]
    exact sdiv_smul (g • x) x
  have hζχ : ζ = kummerMonodromyCharacter M S n w j hj hinterior hn (xi ≫ genericMap) g :=
    (kummerGeometricRootAction_existsUnique M S n w j hj hinterior hn (xi ≫ genericMap) x (g •
      x)).unique hζx hχx
  rw [← hζχ]
  exact hζ

end AlgebraicCurve.CurveModel.OpenKummer
