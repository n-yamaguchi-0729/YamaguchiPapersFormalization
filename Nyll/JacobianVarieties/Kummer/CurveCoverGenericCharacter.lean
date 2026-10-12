/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.CurveCoverCharacter
import Nyll.JacobianVarieties.Kummer.CurveCoverTorsor
import Nyll.JacobianVarieties.Kummer.CurveCoverAction
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

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open JacobianVarieties.Kummer EtaleFundamentalGroups.Cohomology
open scoped FintypeCatDiscrete

namespace AlgebraicCurve.CurveModel

attribute [local instance] IsSepClosure.sep_closed

variable {K : Type u} [Field K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (n : ℕ+) (u : Pic0.kummerUnits K F n)
  {Ω : Type u} [Field Ω] [Algebra M.C.functionField Ω]
  (β : Ω) (hβ : β ^ (n : ℕ) = algebraMap M.C.functionField Ω (M.ffEquiv (u.val : F)))

private def genericKummerRootLift :
    AdjoinRoot (Polynomial.X ^ (n : ℕ) -
      Polynomial.C (M.ffEquiv (u.val : F)) : Polynomial M.C.functionField) →ₐ[M.C.functionField]
        Ω :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId M.C.functionField Ω) β (by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    exact sub_eq_zero.mpr hβ)

private theorem genericKummerRootLift_root :
    genericKummerRootLift M n u β hβ (AdjoinRoot.root _) = β :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

private def genericKummerRootPoint :
    Spec (.of Ω) ⟶ (M.kummerGenericMap n u).normalization :=
  Spec.map (CommRingCat.ofHom (genericKummerRootLift M n u β hβ).toRingHom) ≫
    (M.kummerGenericMap n u).toNormalization

private theorem genericKummerRootPoint_over :
    genericKummerRootPoint M n u β hβ ≫ (M.kummerGenericMap n u).fromNormalization =
      Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω)) ≫
        M.C.fromSpecStalk (genericPoint M.C) := by
  rw [genericKummerRootPoint, Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
  change Spec.map (CommRingCat.ofHom (genericKummerRootLift M n u β hβ).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField _)) ≫
      M.C.fromSpecStalk (genericPoint M.C)) = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hmap : (genericKummerRootLift M n u β hβ).toRingHom.comp
      (algebraMap M.C.functionField _) = algebraMap M.C.functionField Ω := by
    apply RingHom.ext
    intro a
    exact (genericKummerRootLift M n u β hβ).commutes a
  exact congrArg (fun φ : M.C.functionField →+* Ω =>
    Spec.map (CommRingCat.ofHom φ) ≫ M.C.fromSpecStalk (genericPoint M.C)) hmap

private theorem genericKummerRootPoint_scale
    (ζ : rootsOfUnity (n : ℕ) K) (σ : Ω ≃ₐ[M.C.functionField] Ω)
    (hscale : algebraMap M.C.functionField Ω
      (baseToFunctionField M.toBase ((ζ : Kˣ) : K)) * β = σ β) :
    genericKummerRootPoint M n u β hβ ≫ (M.kummerNormalizationRootScale n u ζ).hom =
      Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ genericKummerRootPoint M n u β hβ := by
  let a := M.ffEquiv (u.val : F)
  let η : rootsOfUnity (n : ℕ) M.C.functionField :=
    restrictRootsOfUnity (baseToFunctionField M.toBase) (n : ℕ) ζ
  let l := genericKummerRootLift M n u β hβ
  have halg : l.comp (kummerRootScale (n : ℕ) a η) = σ.toAlgHom.comp l := by
    apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, kummerRootScale_root, map_mul, AlgHom.commutes,
      genericKummerRootLift_root, AlgHom.comp_apply, genericKummerRootLift_root]
    exact hscale
  have hring := congrArg AlgHom.toRingHom halg
  change l.toRingHom.comp (kummerRootScale (n : ℕ) a η).toRingHom =
    (σ : Ω →+* Ω).comp l.toRingHom at hring
  rw [genericKummerRootPoint, Category.assoc, M.toNormalization_kummerNormalizationRootScale]
  rw [← Category.assoc, ← Category.assoc]
  apply congrArg (· ≫ (M.kummerGenericMap n u).toNormalization)
  change Spec.map (CommRingCat.ofHom l.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (kummerRootScale (n : ℕ) a η).toRingHom) = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, hring]

variable [IsSepClosed K]

include hβ

/-- At the actual geometric generic point, the Kummer monodromy character
multiplies a chosen root β by exactly the factor that sends β to σ β. -/
theorem kummerMonodromyCharacter_generic_mul_root
    [IsSepClosure M.C.functionField Ω] (hn : IsUnit ((n : ℕ) : K))
    (σ : Ω ≃ₐ[M.C.functionField] Ω) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let xi := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω))
    let j := M.C.fromSpecStalk (genericPoint M.C)
    let g := FiniteEtale.fundamentalGroupHom j xi
      (toAut (FiniteEtale.fiber xi) (Ω ≃ₐ[M.C.functionField] Ω) σ)
    algebraMap M.C.functionField Ω (baseToFunctionField M.toBase
      ((M.kummerMonodromyCharacter n u hn (xi ≫ j) g : Kˣ) : K)) * β = σ β := by
  intro tμ xi j g
  let T := M.kummerGeometricRootTorsor n u hn (xi ≫ j)
  have := M.kummerGeometricRootAction_commutes n u hn (xi ≫ j)
  let ι : K →+* Ω := (algebraMap M.C.functionField Ω).comp (baseToFunctionField M.toBase)
  have hβ0 : β ≠ 0 := by
    intro hz
    have hzero : algebraMap M.C.functionField Ω (M.ffEquiv (u.val : F)) = 0 := by
      rw [← hβ, hz, zero_pow n.ne_zero]
    have hzero' : M.ffEquiv (u.val : F) = 0 :=
      (algebraMap M.C.functionField Ω).injective
        (hzero.trans (map_zero (algebraMap M.C.functionField Ω)).symm)
    exact (Units.ne_zero u.val) (M.ffEquiv.injective
      (hzero'.trans (map_zero M.ffEquiv).symm))
  have hpow : β ^ (n : ℕ) = (σ β) ^ (n : ℕ) := by
    rw [← map_pow, hβ, AlgEquiv.commutes]
  obtain ⟨ζ, hζ, _⟩ := EtaleFundamentalGroups.Kummer.existsUnique_rootScale
    ι n hn β (σ β) hβ0 hpow
  let W := M.kummerCover n hn u
  let s := genericKummerRootPoint M n u β hβ
  let e := FiniteEtale.fiberObjEquivHom (xi ≫ j) W
  let x : (FiniteEtale.fiber (xi ≫ j)).obj W :=
    e.symm (Over.homMk s (genericKummerRootPoint_over M n u β hβ))
  have hx : (e x).left = s := congrArg (fun q => q.left) (e.apply_symm_apply _)
  have hζx : ζ • x = g • x := by
    apply e.injective
    apply Over.OverMorphism.ext
    have hleft := congrArg (fun q => q.left)
      (FiniteEtale.fiberObjEquivHom_naturality (xi ≫ j)
        (M.kummerCoverRootScale n u hn ζ).hom x)
    have hright := FiniteEtale.fundamentalGroupHom_field_fiberLift j W σ x
    change (e x).left ≫ (M.kummerNormalizationRootScale n u ζ).hom =
      (e (ζ • x)).left at hleft
    change (e (g • x)).left = Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
      (e x).left at hright
    exact hleft.symm.trans ((congrArg (· ≫ (M.kummerNormalizationRootScale n u ζ).hom) hx).trans
      ((genericKummerRootPoint_scale M n u β hβ ζ σ hζ).trans
        ((congrArg (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ ·) hx.symm).trans
          hright.symm)))
  have hχx : M.kummerMonodromyCharacter n u hn (xi ≫ j) g • x = g • x := by
    rw [M.kummerMonodromyCharacter_eq_torsorCharacter n u hn (xi ≫ j) x]
    exact sdiv_smul (g • x) x
  have hζχ : ζ = M.kummerMonodromyCharacter n u hn (xi ≫ j) g :=
    (M.kummerGeometricRootAction_existsUnique n u hn (xi ≫ j) x (g • x)).unique hζx hχx
  rw [← hζχ]
  exact hζ

end AlgebraicCurve.CurveModel
