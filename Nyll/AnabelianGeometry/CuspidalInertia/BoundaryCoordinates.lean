/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.CuspidalInertia.BoundaryRetraction
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.LinearCombination

/-!
# Free coordinates for the reduced boundary module

Choosing one boundary label identifies the module modulo its diagonal with
functions on all remaining labels. This gives an integral coordinate system;
in particular, no inversion of the number of boundary points is needed.
-/

namespace AnabelianGeometry.CuspidalInertia

universe u v

variable {R : Type u} [CommRing R] {ι : Type v}

/-- Coordinates relative to one distinguished boundary label. -/
def boundaryCoordinates (base : ι) :
    BoundaryModule R ι →ₗ[R] ({i : ι // i ≠ base} → R) :=
  LinearMap.pi (fun i => boundaryDifference (R := R) i.1 base)

/-- The relative coordinates separate all classes modulo the diagonal. -/
theorem boundaryCoordinates_injective (base : ι) :
    Function.Injective (boundaryCoordinates (R := R) base) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro f g h
  apply (Submodule.Quotient.eq (p := boundaryDiagonal R ι)).mpr
  refine ⟨f base - g base, ?_⟩
  intro i
  by_cases hi : i = base
  · subst i
    rfl
  · have hd := congrFun h ⟨i, hi⟩
    change f i - f base = g i - g base at hd
    change f i - g i = f base - g base
    linear_combination hd

/-- Every tuple of relative boundary coordinates has a representative. -/
theorem boundaryCoordinates_surjective (base : ι) :
    Function.Surjective (boundaryCoordinates (R := R) base) := by
  classical
  intro v
  let f : ι → R := fun i => if hi : i = base then 0 else v ⟨i, hi⟩
  refine ⟨Submodule.Quotient.mk f, ?_⟩
  funext i
  change f i.1 - f base = v i
  dsimp only [f]
  rw [dite_eq_right i.2, dite_eq_left rfl, sub_zero]

/-- An integral coordinate equivalence for the boundary relation module. -/
noncomputable def boundaryCoordinatesEquiv (base : ι) :
    BoundaryModule R ι ≃ₗ[R] ({i : ι // i ≠ base} → R) :=
  LinearEquiv.ofBijective (boundaryCoordinates base)
    ⟨boundaryCoordinates_injective base, boundaryCoordinates_surjective base⟩

end AnabelianGeometry.CuspidalInertia
