/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.CurveCoverRamification
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.RationalOneBranch
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_ratFunc
import Mathlib.RingTheory.EssentialFiniteness

/-!
# Function fields of etale covers of a proper rational curve

In characteristic zero, a finite etale surjective morphism from a smooth proper integral
curve model to a rational curve model induces an isomorphism of function fields. The
isomorphism retains the actual morphism's correspondence between points and places.
This conclusion uses the stalk comparison and Riemann--Hurwitz, not a fundamental-group
presentation or an assumed triviality of covers.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve

namespace AnabelianGeometry.GeometricFundamentalGroup

/-- A finite etale cover of a proper rational curve in characteristic zero has the same
function field, with the isomorphism compatible with the actual map on curve points. -/
theorem exists_functionFieldEquiv_of_finite_etale_rational
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field F]
    [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (M : CurveModel K (RatFunc K)) (N : CurveModel K F)
    (π : N.C ⟶ M.C) (hπ : π ≫ M.toBase = N.toBase)
    [IsFinite π] [Etale π] (hsurj : Function.Surjective π.base) :
    ∃ e : RatFunc K ≃ₐ[K] F, ∃ hint : e.toAlgHom.toRingHom.IsIntegral,
      ∀ w : Place K F,
        (M.pointEquivPlace.symm (w.restrictAlong e.toAlgHom hint)).1 =
          (N.pointEquivPlace.symm w).1 ≫ π := by
  have rationalCurve : IsCurveOver K (RatFunc K) := isCurveOver_ratFunc K
  have rationalLocalization : Algebra.EssFiniteType (Polynomial K) (RatFunc K) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc K) (nonZeroDivisors (Polynomial K))
  have rationalFiniteType : Algebra.EssFiniteType K (RatFunc K) :=
    Algebra.EssFiniteType.comp K (Polynomial K) (RatFunc K)
  obtain ⟨φ, hfin, hint, hpoints, hunram⟩ :=
    exists_functionFieldMap_unramified_of_finite_etale M N π hπ hsurj
  let fieldAlgebra : Algebra (RatFunc K) F := algebraAlong φ
  have fieldTower : IsScalarTower K (RatFunc K) F := isScalarTower_along φ
  have fieldFinite : Module.Finite (RatFunc K) F := hfin
  have hbij : Function.Bijective φ :=
    bijective_algebraMap_of_one_branch (RationalFunctionField.placeOfPoint K 0)
      (fun w _ => hunram w)
  exact ⟨AlgEquiv.ofBijective φ hbij, hint, hpoints⟩

end AnabelianGeometry.GeometricFundamentalGroup
