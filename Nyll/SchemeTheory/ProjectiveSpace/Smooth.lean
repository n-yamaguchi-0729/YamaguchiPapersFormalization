/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Smooth.Basic

/-!
# Smoothness of projective space

The standard affine charts are polynomial algebras over the coefficient ring.
Their existing algebra equivalences identify the chart structure morphisms,
so smoothness glues over the standard affine open cover.
-/

noncomputable section

universe u

open CategoryTheory HomogeneousLocalization
open AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Projective space is smooth over its coefficient spectrum. -/
theorem smooth_π (R : Type u) [CommRing R] (n : ℕ) : Smooth (π R n) := by
  have : IsZariskiLocalAtSource (@Smooth : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth.{u}) (Q := RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth)
    (affineOpenCover R n).openCover
  change ∀ j : Fin (n + 1), Smooth
    (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X j) (X_mem_one R n j) one_pos ≫ π R n)
  intro j
  rw [awayι_comp_π R n j, HasRingHomProperty.Spec_iff (P := @Smooth)]
  change RingHom.Smooth
    (algebraMap R (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X j)))
  rw [RingHom.smooth_algebraMap]
  have : Algebra.Smooth R (MvPolynomial {k : Fin (n + 1) // k ≠ j} R) :=
    ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.of_equiv (awayChartEquiv (S := R) n j)

end AlgebraicGeometry.ProjSpace
