/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.CuspidalInertia.BoundaryModule
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Ring

/-!
# Integral retractions of boundary coordinates

Differences of coordinate evaluations vanish on the diagonal relation and
therefore descend to the reduced boundary module. They recover a boundary
coefficient integrally, without division by the number of punctures.
-/

namespace AnabelianGeometry.CuspidalInertia

universe u v

variable {R : Type u} [CommRing R] {ι : Type v}

/-- Difference of two evaluations on the boundary permutation module. -/
def boundaryEvaluationDifference (i j : ι) : (ι → R) →ₗ[R] R where
  toFun f := f i - f j
  map_add' f g := by
    change (f i + g i) - (f j + g j) = (f i - f j) + (g i - g j)
    ring
  map_smul' a f := by
    change a * f i - a * f j = a * (f i - f j)
    exact (mul_sub a (f i) (f j)).symm

/-- Difference of evaluations descends through the diagonal relation. -/
def boundaryDifference (i j : ι) : BoundaryModule R ι →ₗ[R] R :=
  (boundaryDiagonal R ι).liftQ (boundaryEvaluationDifference i j) (by
    rintro f ⟨a, ha⟩
    change f i - f j = 0
    rw [ha i, ha j, sub_self])

/-- Evaluating a quotient representative gives its coordinate difference. -/
theorem boundaryDifference_mk (i j : ι) (f : ι → R) :
    boundaryDifference (R := R) i j (Submodule.Quotient.mk f : BoundaryModule R ι) =
      f i - f j := rfl

/-- The descended coordinate difference is an integral left inverse to a
boundary coordinate whenever the other label is distinct. -/
theorem boundaryDifference_boundaryClass [DecidableEq ι]
    (i j : ι) (hji : j ≠ i) (a : R) :
    boundaryDifference (R := R) i j (boundaryClass i a : BoundaryModule R ι) = a := by
  change (if i = i then a else 0) - (if j = i then a else 0) = a
  rw [ite_eq_left rfl, ite_eq_right hji, sub_zero]

end AnabelianGeometry.CuspidalInertia
