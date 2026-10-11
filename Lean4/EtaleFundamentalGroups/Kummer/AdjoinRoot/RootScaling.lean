/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Algebra.Equiv

/-!
# Actual root-of-unity automorphisms of the Kummer algebra

Multiplication of the adjoined root by a root of unity gives an actual algebra
automorphism. No irreducibility or domain hypothesis on the Kummer algebra is
needed, so the construction includes disconnected Kummer covers.
-/

noncomputable section

universe u

namespace JacobianVarieties.Kummer

variable {R : Type u} [CommRing R] (n : ℕ) (a : R)

private theorem kummerRoot_pow :
    AdjoinRoot.root (Polynomial.X ^ n - Polynomial.C a : Polynomial R) ^ n =
      algebraMap R (AdjoinRoot (Polynomial.X ^ n - Polynomial.C a : Polynomial R)) a := by
  have h := AdjoinRoot.eval₂_root (Polynomial.X ^ n - Polynomial.C a : Polynomial R)
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, sub_eq_zero] at h
  exact h

/-- Scale the adjoined Kummer root by the specified root of unity. -/
def kummerRootScale (ζ : rootsOfUnity n R) :
    AdjoinRoot (Polynomial.X ^ n - Polynomial.C a : Polynomial R) →ₐ[R]
      AdjoinRoot (Polynomial.X ^ n - Polynomial.C a : Polynomial R) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _)
    (algebraMap R _ (ζ.val : R) * AdjoinRoot.root _) (by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, mul_pow, ← map_pow,
        (mem_rootsOfUnity' n ζ.val).mp ζ.property, map_one, one_mul, kummerRoot_pow]
      exact sub_self _)

/-- The constructed algebra endomorphism sends the actual root to its scale. -/
theorem kummerRootScale_root (ζ : rootsOfUnity n R) :
    kummerRootScale n a ζ (AdjoinRoot.root _) =
      algebraMap R _ (ζ.val : R) * AdjoinRoot.root _ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Scaling by one is the identity on the original Kummer algebra. -/
theorem kummerRootScale_one : kummerRootScale n a 1 = AlgHom.id R _ := by
  apply AdjoinRoot.algHom_ext
  rw [kummerRootScale_root, AlgHom.id_apply]
  change algebraMap R _ (1 : R) * _ = _
  rw [map_one, one_mul]

/-- Composition of the actual root scalings is multiplication of their coefficients. -/
theorem kummerRootScale_mul (ζ η : rootsOfUnity n R) :
    kummerRootScale n a (ζ * η) = (kummerRootScale n a ζ).comp (kummerRootScale n a η) := by
  apply AdjoinRoot.algHom_ext
  rw [AlgHom.comp_apply, kummerRootScale_root n a η, map_mul, AlgHom.commutes,
    kummerRootScale_root, kummerRootScale_root]
  change algebraMap R _ ((ζ.val : R) * (η.val : R)) * _ = _
  rw [map_mul]
  exact (mul_assoc _ _ _).trans (mul_left_comm _ _ _)

/-- Every root scaling is an algebra automorphism, with inverse scaling by the inverse root. -/
def kummerRootScaleEquiv (ζ : rootsOfUnity n R) :
    AdjoinRoot (Polynomial.X ^ n - Polynomial.C a : Polynomial R) ≃ₐ[R]
      AdjoinRoot (Polynomial.X ^ n - Polynomial.C a : Polynomial R) :=
  AlgEquiv.ofAlgHom (kummerRootScale n a ζ) (kummerRootScale n a ζ⁻¹)
    (by rw [← kummerRootScale_mul, mul_inv_cancel, kummerRootScale_one])
    (by rw [← kummerRootScale_mul, inv_mul_cancel, kummerRootScale_one])

end JacobianVarieties.Kummer
