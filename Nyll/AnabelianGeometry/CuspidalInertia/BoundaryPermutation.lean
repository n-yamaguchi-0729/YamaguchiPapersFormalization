/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.CuspidalInertia.BoundaryModule
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Permutations of the reduced boundary module

Permuting boundary labels preserves the diagonal relation and induces a
linear equivalence on the reduced boundary module. The equivalence sends
each boundary coordinate to its permuted coordinate.
-/

namespace AnabelianGeometry.CuspidalInertia

universe u v

variable {R : Type u} [CommRing R] {ι : Type v}

/-- Reindex the full boundary permutation module. -/
def boundaryReindex (e : ι ≃ ι) : (ι → R) →ₗ[R] (ι → R) where
  toFun f j := f (e.symm j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The induced map on the quotient by the diagonal relation. -/
def boundaryPermutation (e : ι ≃ ι) : BoundaryModule R ι →ₗ[R] BoundaryModule R ι :=
  (boundaryDiagonal R ι).mapQ (boundaryDiagonal R ι) (boundaryReindex e) (by
    rintro f ⟨a, ha⟩
    exact ⟨a, fun j => ha (e.symm j)⟩)

/-- A permutation acts invertibly on the reduced boundary module. -/
def boundaryPermutationEquiv (e : ι ≃ ι) :
    BoundaryModule R ι ≃ₗ[R] BoundaryModule R ι where
  toLinearMap := boundaryPermutation (R := R) e
  invFun := boundaryPermutation (R := R) e.symm
  left_inv x := by
    refine Quotient.inductionOn x ?_
    intro f
    change (Submodule.Quotient.mk (fun j => f (e.symm (e j))) : BoundaryModule R ι) =
      Submodule.Quotient.mk f
    congr 1
    funext j
    rw [e.symm_apply_apply]
  right_inv x := by
    refine Quotient.inductionOn x ?_
    intro f
    change (Submodule.Quotient.mk (fun j => f (e (e.symm j))) : BoundaryModule R ι) =
      Submodule.Quotient.mk f
    congr 1
    funext j
    rw [e.apply_symm_apply]

/-- Boundary coordinates are permuted with their labels, with coefficients unchanged. -/
theorem boundaryPermutation_boundaryClass [DecidableEq ι]
    (e : ι ≃ ι) (i : ι) (a : R) :
    boundaryPermutation (R := R) e (boundaryClass i a) = boundaryClass (e i) a := by
  change (Submodule.Quotient.mk (fun j => if e.symm j = i then a else 0) :
    BoundaryModule R ι) = Submodule.Quotient.mk (fun j => if j = e i then a else 0)
  congr 1
  funext j
  by_cases h : j = e i
  · have h' : e.symm j = i := e.symm_apply_eq.mpr h
    rw [ite_eq_left h', ite_eq_left h]
  · have h' : e.symm j ≠ i := fun h' => h (e.symm_apply_eq.mp h')
    rw [ite_eq_right h', ite_eq_right h]

end AnabelianGeometry.CuspidalInertia
