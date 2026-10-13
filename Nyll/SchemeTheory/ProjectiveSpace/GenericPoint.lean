/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.Topology.Sober

/-!
# The generic point of projective space over a domain

The zero homogeneous ideal is prime and relevant. Its inclusion in every
homogeneous prime proves that its closure is the whole projective space.
-/

noncomputable section

universe u

open TopologicalSpace

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The zero homogeneous prime of projective space over a domain. -/
def genericPoint (R : Type u) [CommRing R] [IsDomain R] (n : ℕ) :
    Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) where
  asHomogeneousIdeal := ⊥
  isPrime := Ideal.isPrime_bot
  not_irrelevant_le := by
    intro h
    have hX := h (HomogeneousIdeal.mem_irrelevant_of_mem
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (show 0 < (1 : ℕ) from Nat.zero_lt_one) (X_mem_one R n 0))
    exact MvPolynomial.X_ne_zero (0 : Fin (n + 1))
      (show MvPolynomial.X (0 : Fin (n + 1)) = (0 : MvPolynomial (Fin (n + 1)) R)
        from hX)

/-- Every point of projective space specializes from the zero homogeneous prime. -/
theorem isGenericPoint_genericPoint (R : Type u) [CommRing R] [IsDomain R] (n : ℕ) :
    IsGenericPoint (genericPoint R n) Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  apply (ProjectiveSpectrum.le_iff_mem_closure
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (genericPoint R n) x).mp
  change (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) ≤ _
  exact bot_le

/-- Projective space over a domain is irreducible. -/
theorem irreducibleSpace (R : Type u) [CommRing R] [IsDomain R] (n : ℕ) :
    IrreducibleSpace (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :=
  (irreducibleSpace_def _).mpr (isGenericPoint_genericPoint R n).isIrreducible

end AlgebraicGeometry.ProjSpace
