/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.FiniteType

/-!
# Finite-valued points of a finitely generated algebra

A homomorphism is determined by its values on finitely many algebra
generators. This gives the affine finiteness input for rational points over
finite fields, without a zero-dimensional or module-finite hypothesis.
-/

namespace AnabelianGeometry.WeightFiltration

/-- A finite-type algebra has finitely many algebra maps to a finite algebra. -/
theorem finite_algHom_of_finiteType
    (R A B : Type*) [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] [Finite B] :
    Finite (A →ₐ[R] B) := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R A).FG)
  exact Finite.of_injective (fun f : A →ₐ[R] B => fun a : s => f a) (by
    intro f g h
    apply AlgHom.ext_of_adjoin_eq_top hs
    intro a ha
    exact congrFun h ⟨a, ha⟩)

end AnabelianGeometry.WeightFiltration
