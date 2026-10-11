/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.Cech.Scheme_TwoAffineOpenCover_finrank_cechDiff_baseChange_of_isAlgClosed
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover

/-!
# Geometric genus and structure-sheaf cohomology over an arbitrary field

The genus is defined by the actual function field of the base change to an
algebraic closure. It needs neither a rational point nor a chosen affine cover.
For a smooth proper geometrically integral curve it equals the dimension of
structure-sheaf first cohomology on every two-affine cover of the original curve.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.SmoothProperCurve

/-- The genus of the geometric function field, using its actual repartition cohomology. -/
def geometricGenus (K : Type u) [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [GeometricallyIntegral c] : ℕ :=
  let := (AlgebraicCurve.baseToFunctionField (baseChange K c (AlgebraicClosure K))).toAlgebra
  AlgebraicCurve.genusFF (AlgebraicClosure K)
    (pullback c (specMap K (AlgebraicClosure K))).functionField

/-- Scalar extension preserves the dimension of the actual Cech cokernel, identifying
the point-free geometric genus with first cohomology over the original field. -/
theorem finrank_H1_eq_geometricGenus (K : Type u) [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (𝒱 : C.TwoAffineOpenCover) :
    Module.finrank K (𝒱.structureSheafSections c).H1 = geometricGenus K c := by
  let Ω := AlgebraicClosure K
  let d := (𝒱.structureSheafSections c).cechDiff
  have hex : Function.Exact d (LinearMap.range d).mkQ :=
    LinearMap.exact_map_mkQ_range d
  have hsurj : Function.Surjective (LinearMap.range d).mkQ :=
    Submodule.mkQ_surjective (LinearMap.range d)
  have hexΩ : Function.Exact (d.baseChange Ω)
      ((LinearMap.range d).mkQ.baseChange Ω) := by
    have ht := lTensor_exact Ω hex hsurj
    rwa [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at ht
  let e := hexΩ.linearEquivOfSurjective (LinearMap.baseChange_surjective Ω hsurj)
  have hgenus := (𝒱.finrank_cechDiff_baseChange_of_isAlgClosed c Ω).2.2
  calc
    Module.finrank K (𝒱.structureSheafSections c).H1 =
        Module.finrank Ω (Ω ⊗[K] (𝒱.structureSheafSections c).H1) :=
      Module.finrank_baseChange.symm
    _ = Module.finrank Ω ((Ω ⊗[K] (𝒱.cover c).A01) ⧸
        LinearMap.range (d.baseChange Ω)) := e.finrank_eq.symm
    _ = geometricGenus K c := hgenus

end AlgebraicGeometry.SmoothProperCurve
