/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.Data.Set.Image
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FinCases

/-!
# The projective point of a nonzero coordinate pair over a field

The homogeneous core of the kernel of evaluation at `(u,v)` is a homogeneous
prime ideal. A nonzero coordinate prevents this ideal from containing the
irrelevant ideal, so it defines a point of the actual projective scheme.
Membership of a homogeneous polynomial is exactly vanishing at `(u,v)`.
In particular, the equation `t*T₀-s*T₁` vanishes at this point if and only if
`t*u-s*v = 0`.

This constructs the points used in the first assertion of Lemma 2.3 of
Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
The uniqueness, closedness, and intersection-length comparisons are separate results.
-/

noncomputable section

namespace ShimizuYamaguchi26BranchedCoverings

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

/-- Both homogeneous coordinates cannot belong to a projective point's ideal. -/
theorem projectiveLine_not_both_coordinates_mem (x : ProjectiveLine R)
    (hzero : MvPolynomial.X (0 : Fin 2) ∈ x.asHomogeneousIdeal)
    (hone : MvPolynomial.X (1 : Fin 2) ∈ x.asHomogeneousIdeal) : False := by
  have hspan : Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) R)) ≤
      x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le, Set.range_subset_iff]
    intro i
    fin_cases i
    · exact hzero
    · exact hone
  exact x.not_irrelevant_le
    ((AlgebraicGeometry.ProjSpace.irrelevant_le_span_X R 1).trans hspan)

variable {k : Type u} [Field k]

/-- Evaluation at the ordered pair of homogeneous coordinates `(u,v)`. -/
def fieldSectionEvaluation (u v : k) : MvPolynomial (Fin 2) k →+* k :=
  MvPolynomial.eval (fun i : Fin 2 => if i = 0 then u else v)

/-- Evaluation of the first homogeneous coordinate. -/
theorem fieldSectionEvaluation_X_zero (u v : k) :
    fieldSectionEvaluation u v (MvPolynomial.X 0) = u := by
  change MvPolynomial.eval _ (MvPolynomial.X (0 : Fin 2)) = _
  rw [MvPolynomial.eval_X, ite_eq_left (rfl : (0 : Fin 2) = 0)]

/-- Evaluation of the second homogeneous coordinate. -/
theorem fieldSectionEvaluation_X_one (u v : k) :
    fieldSectionEvaluation u v (MvPolynomial.X 1) = v := by
  change MvPolynomial.eval _ (MvPolynomial.X (1 : Fin 2)) = _
  rw [MvPolynomial.eval_X, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]

/-- Evaluation of a homogeneous linear section equation. -/
theorem fieldSectionEvaluation_linearSectionEquation (u v s t : k) :
    fieldSectionEvaluation u v (linearSectionEquation s t) = t * u - s * v := by
  rw [linearSectionEquation, map_sub, map_mul, map_mul,
    fieldSectionEvaluation_X_zero, fieldSectionEvaluation_X_one]
  simp only [fieldSectionEvaluation, MvPolynomial.eval_C]

/-- The actual projective-scheme point determined by a nonzero coordinate pair.
Its homogeneous ideal is the homogeneous core of the evaluation kernel. -/
def fieldSectionPoint (u v : k) (huv : u ≠ 0 ∨ v ≠ 0) : ProjectiveLine k where
  asHomogeneousIdeal :=
    (RingHom.ker (fieldSectionEvaluation u v)).homogeneousCore
      (MvPolynomial.homogeneousSubmodule (Fin 2) k)
  isPrime := (RingHom.ker_isPrime (fieldSectionEvaluation u v)).homogeneousCore
  not_irrelevant_le := by
    intro hle
    have hcoordinates : ∀ i : Fin 2, fieldSectionEvaluation u v (MvPolynomial.X i) = 0 := by
      intro i
      have hmem : MvPolynomial.X i ∈ RingHom.ker (fieldSectionEvaluation u v) :=
        Ideal.toIdeal_homogeneousCore_le
          (MvPolynomial.homogeneousSubmodule (Fin 2) k)
          (RingHom.ker (fieldSectionEvaluation u v))
          (hle (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
            (AlgebraicGeometry.ProjSpace.X_mem_one k 1 i)))
      exact RingHom.mem_ker.mp hmem
    rcases huv with hu | hv
    · exact hu ((fieldSectionEvaluation_X_zero u v).symm.trans (hcoordinates 0))
    · exact hv ((fieldSectionEvaluation_X_one u v).symm.trans (hcoordinates 1))

/-- A homogeneous polynomial belongs to the constructed point exactly when
its evaluation at the original coordinates is zero. -/
theorem homogeneous_mem_fieldSectionPoint_iff
    (u v : k) (huv : u ≠ 0 ∨ v ≠ 0)
    (f : MvPolynomial (Fin 2) k) {n : ℕ}
    (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k n) :
    f ∈ (fieldSectionPoint u v huv).asHomogeneousIdeal ↔
      fieldSectionEvaluation u v f = 0 := by
  constructor
  · intro h
    change f ∈ (RingHom.ker (fieldSectionEvaluation u v)).homogeneousCore
      (MvPolynomial.homogeneousSubmodule (Fin 2) k) at h
    exact RingHom.mem_ker.mp (Ideal.toIdeal_homogeneousCore_le
      (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (RingHom.ker (fieldSectionEvaluation u v)) h)
  · intro h
    change f ∈ (RingHom.ker (fieldSectionEvaluation u v)).homogeneousCore
      (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨n, hf⟩
      (RingHom.mem_ker.mpr h)

/-- The linear equation of `(s,t)` contains the constructed point of `(u,v)`
exactly when their coordinate determinant vanishes. -/
theorem linearSectionEquation_mem_fieldSectionPoint_iff
    (u v s t : k) (huv : u ≠ 0 ∨ v ≠ 0) :
    linearSectionEquation s t ∈ (fieldSectionPoint u v huv).asHomogeneousIdeal ↔
      t * u - s * v = 0 := by
  rw [homogeneous_mem_fieldSectionPoint_iff u v huv _
      (linearSectionEquation_mem_one s t),
    fieldSectionEvaluation_linearSectionEquation]

/-- The constructed point lies on its own homogeneous section equation. -/
theorem linearSectionEquation_mem_fieldSectionPoint
    (u v : k) (huv : u ≠ 0 ∨ v ≠ 0) :
    linearSectionEquation u v ∈ (fieldSectionPoint u v huv).asHomogeneousIdeal := by
  rw [linearSectionEquation_mem_fieldSectionPoint_iff]
  exact sub_eq_zero.mpr (mul_comm v u)

end ShimizuYamaguchi26BranchedCoverings
