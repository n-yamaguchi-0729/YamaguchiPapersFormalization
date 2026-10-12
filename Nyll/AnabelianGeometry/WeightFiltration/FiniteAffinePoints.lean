/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.FiniteAlgebraHom
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Finiteness of actual affine points over finite rings

This is finiteness of morphisms over the base, not finiteness of the
underlying topological fiber. The affine scheme may have positive dimension.
-/

open AlgebraicGeometry CategoryTheory NeronModelInfra

namespace AnabelianGeometry.WeightFiltration

/-- The actual finite-valued points of a finite-type affine scheme form a
finite type, by the spectrum/algebra-homomorphism equivalence. -/
theorem finite_affine_points
    (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] [Finite B] :
    Finite (SchemeHomOver (Spec.algebraMap R B) (Spec.algebraMap R A)) := by
  have : Finite (A →ₐ[R] B) := finite_algHom_of_finiteType R A B
  exact Finite.of_injective (Spec.homEquivAlgHom (R := R) (A := A) (B := B))
    (Spec.homEquivAlgHom (R := R) (A := A) (B := B)).injective

end AnabelianGeometry.WeightFiltration
