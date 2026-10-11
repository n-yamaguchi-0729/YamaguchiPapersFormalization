/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.AbsoluteModPTwoCocycleOfTsen
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_exists_separating_transcendental
import Nyll.AlgebraicCurves.Models.IsCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one

/-!
# Actual smooth-curve function fields have vanishing absolute mod-p H²

The field is the scheme's actual function field. Smooth relative dimension
one supplies its separating transcendence parameter via the existing
geometric Kähler-differential calculation. Tsen and the already proved
continuous-cocycle argument then give the vanishing.

This is a function-field statement, not yet the comparison with the
higher étale cohomology of the curve.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
open AlgebraicCurves.Models.Proofs
open IsCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one

namespace AlgebraicCurve

/-- The actual function field of an integral smooth curve over an
algebraically closed characteristic-zero field has zero absolute
continuous mod-p H². No rational parameter or finite-extension
presentation is assumed in the statement. -/
theorem functionField_absoluteGalois_continuousH2_eq_zero
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 c]
    (p : ℕ+) [Fact (p : ℕ).Prime]
    (v : ClassFieldTower.Cohomology.continuousCohomologyZModPLifted
      (p : ℕ) (Field.absoluteGaloisGroup C.functionField) 2) : v = 0 := by
  let algKF : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
  have : Algebra.EssFiniteType K C.functionField :=
    (SmoothModelFunctionField.stageA c).1
  have : IsCurveOver K C.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c
      (RingEquiv.refl C.functionField) (fun _ => rfl)
  obtain ⟨x, hx, hfin, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := C.functionField)
  exact absoluteGalois_continuousH2_eq_zero_of_transcendental_of_finiteDimensional
    K x hx hfin p v

end AlgebraicCurve
