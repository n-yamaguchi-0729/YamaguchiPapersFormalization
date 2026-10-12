/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.CurveCoverGenericCharacter
import Nyll.JacobianVarieties.Kummer.OpenCurveCoverGenericCharacter
import Nyll.AlgebraicCurves.Models.FunctionFieldScalarFunctoriality

/-!
# Restriction of actual generic Kummer characters to an open curve

The proper and open normalization covers give the same root quotient under
restriction of field automorphisms. The proof computes both actual
monodromy characters on one common root.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve

namespace AnabelianGeometry.WeightFiltration

/-- The actual proper and open Kummer monodromy characters agree at the
common geometric generic point after scalar restriction. -/
theorem proper_open_genericKummerCharacter
    {K F : Type} [Field K] [IsSepClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
    (u : Pic0.kummerUnits K F n)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hinterior : ∀ (y : X) (x : closedPoints M.C),
      x.val = j y → M.placeOfPoint x ∉ S)
    [Algebra M.C.functionField X.functionField]
    (hfield : algebraMap M.C.functionField X.functionField = j.functionFieldMap hj)
    {Ω : Type} [Field Ω] [Algebra X.functionField Ω] [Algebra M.C.functionField Ω]
    [IsScalarTower M.C.functionField X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M.C.functionField Ω] [IsSepClosure X.functionField Ω]
    (β : Ω) (hβ : β ^ (n : ℕ) =
      algebraMap M.C.functionField Ω (M.ffEquiv (u.val : F)))
    (hn : IsUnit ((n : ℕ) : K)) (σ : Ω ≃ₐ[X.functionField] Ω) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let ηp := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω))
    let ηo := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let gp := FiniteEtale.fundamentalGroupHom (M.C.fromSpecStalk (genericPoint M.C)) ηp
      (toAut (FiniteEtale.fiber ηp) (Ω ≃ₐ[M.C.functionField] Ω)
        (σ.restrictScalars M.C.functionField))
    let go := FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) ηo
      (toAut (FiniteEtale.fiber ηo) (Ω ≃ₐ[X.functionField] Ω) σ)
    M.kummerMonodromyCharacter n u hn (ηp ≫ M.C.fromSpecStalk (genericPoint M.C)) gp =
      CurveModel.OpenKummer.kummerMonodromyCharacter M S n
        (Pic0.kummerUnitsToOpen S n u) j hj hinterior hn
        (ηo ≫ X.fromSpecStalk (genericPoint X)) go := by
  intro htop ηp ηo gp go
  have hβo : β ^ (n : ℕ) = algebraMap X.functionField Ω
      (j.functionFieldMap hj (M.ffEquiv ((Pic0.kummerUnitsToOpen S n u).val : F))) := by
    change β ^ (n : ℕ) = algebraMap X.functionField Ω
      (j.functionFieldMap hj (M.ffEquiv (u.val : F)))
    rw [← hfield, ← IsScalarTower.algebraMap_apply]
    exact hβ
  have hβ0 : β ≠ 0 := by
    intro hz
    have hzero : algebraMap M.C.functionField Ω (M.ffEquiv (u.val : F)) = 0 := by
      rw [← hβ, hz, zero_pow n.ne_zero]
    have hzero' : M.ffEquiv (u.val : F) = 0 :=
      (algebraMap M.C.functionField Ω).injective
        (hzero.trans (map_zero (algebraMap M.C.functionField Ω)).symm)
    exact Units.ne_zero u.val (M.ffEquiv.injective
      (hzero'.trans (map_zero M.ffEquiv).symm))
  have hcoeff (a : K) :
      algebraMap M.C.functionField Ω (baseToFunctionField M.toBase a) =
        algebraMap X.functionField Ω (baseToFunctionField (j ≫ M.toBase) a) := by
    rw [← Scheme.Hom.functionFieldMap_baseToFunctionField M.toBase j hj a, ← hfield,
      ← IsScalarTower.algebraMap_apply]
  have hp := M.kummerMonodromyCharacter_generic_mul_root n u β hβ hn
    (σ.restrictScalars M.C.functionField)
  have ho := CurveModel.OpenKummer.kummerMonodromyCharacter_generic_mul_root
    M S n (Pic0.kummerUnitsToOpen S n u) j hj hinterior β hβo hn σ
  apply Subtype.ext
  apply Units.ext
  apply ((algebraMap M.C.functionField Ω).comp (baseToFunctionField M.toBase)).injective
  apply (mul_right_cancel₀ hβ0)
  change algebraMap M.C.functionField Ω (baseToFunctionField M.toBase _) * β =
    algebraMap M.C.functionField Ω (baseToFunctionField M.toBase _) * β
  exact hp.trans (ho.symm.trans
    (congrArg (fun z : Ω => z * β) (hcoeff _).symm))

end AnabelianGeometry.WeightFiltration
