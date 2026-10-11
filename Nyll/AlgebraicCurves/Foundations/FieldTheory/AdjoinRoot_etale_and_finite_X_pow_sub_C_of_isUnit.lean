/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AdjoinRoot_etale_and_finite_X_pow_sub_C_of_isUnit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.Tactic.Ring.RingNF

/-!
# Adjoin Root etale and finite X pow sub C of is Unit
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.FieldTheory.Proofs
namespace AdjoinRoot_etale_and_finite_X_pow_sub_C_of_isUnit

universe u

open Polynomial

namespace KummerEtaleSol

variable {R : Type u} [CommRing R]

/-- The standard étale pair for `X ^ n - u` when the exponent and coefficient are units. -/
noncomputable def kummerPair (n : ℕ) (u : R) (hn0 : n ≠ 0) (hn : IsUnit (n : R)) (hu : IsUnit u) :
    StandardEtalePair R where
  f := X ^ n - C u
  monic_f := monic_X_pow_sub_C u hn0
  g := 1
  cond := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0
    refine ⟨C (↑hn.unit⁻¹ * ↑hu.unit⁻¹ : R) * X, - C (↑hu.unit⁻¹ : R), 0, ?_⟩
    have h1 : ((m + 1 : ℕ) : R) * (↑hn.unit⁻¹ : R) = 1 := hn.mul_val_inv
    have h2 : u * (↑hu.unit⁻¹ : R) = 1 := hu.mul_val_inv
    rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero, pow_zero, Nat.add_sub_cancel]
    set a : R := ↑hn.unit⁻¹ with ha
    set b : R := ↑hu.unit⁻¹ with hb
    calc C ((m + 1 : ℕ) : R) * X ^ m * (C (a * b) * X) + (X ^ (m + 1) - C u) * -C b
        = C (((m + 1 : ℕ) : R) * a) * C b * X ^ (m + 1) - C b * X ^ (m + 1) + C (u * b) := by
          simp only [C_mul]; ring
      _ = 1 := by rw [h1, h2, C_1]; ring

lemma kummerPair_f (n : ℕ) (u : R) (hn0 : n ≠ 0) (hn : IsUnit (n : R)) (hu : IsUnit u) :
    (kummerPair n u hn0 hn hu).f = X ^ n - C u := rfl

lemma kummerPair_g (n : ℕ) (u : R) (hn0 : n ≠ 0) (hn : IsUnit (n : R)) (hu : IsUnit u) :
    (kummerPair n u hn0 hn hu).g = 1 := rfl

/-- The standard étale presentation of the Kummer root algebra when the exponent and coefficient
are units. -/
noncomputable def kummerPresentation (n : ℕ) (u : R) (hn0 : n ≠ 0) (hn : IsUnit (n : R))
    (hu : IsUnit u) : StandardEtalePresentation R (AdjoinRoot (X ^ n - C u : R[X])) where
  __ := kummerPair n u hn0 hn hu
  x := AdjoinRoot.root (X ^ n - C u)
  hasMap := ⟨by rw [kummerPair_f, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self],
    by rw [kummerPair_g, map_one]; exact isUnit_one⟩
  lift_bijective := by
    set P := kummerPair n u hn0 hn hu with hP
    have hX : P.HasMap (AdjoinRoot.root (X ^ n - C u)) :=
      ⟨by rw [kummerPair_f, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self],
       by rw [kummerPair_g, map_one]; exact isUnit_one⟩
    have hroot : (X ^ n - C u : R[X]).eval₂ (Algebra.ofId R P.Ring) P.X = 0 := by
      have := P.hasMap_X.1
      rwa [kummerPair_f] at this
    let ψ : AdjoinRoot (X ^ n - C u : R[X]) →ₐ[R] P.Ring :=
      AdjoinRoot.liftAlgHom (X ^ n - C u) (Algebra.ofId R P.Ring) P.X hroot
    have hψroot : ψ (AdjoinRoot.root (X ^ n - C u)) = P.X :=
      AdjoinRoot.liftAlgHom_root (X ^ n - C u) (Algebra.ofId R P.Ring) P.X hroot
    have h1 : (P.lift _ hX).comp ψ = AlgHom.id R _ := by
      apply AdjoinRoot.algHom_ext
      exact (congrArg (P.lift _ hX) hψroot).trans (P.lift_X _ hX)
    have h2 : ψ.comp (P.lift _ hX) = AlgHom.id R _ := by
      apply StandardEtalePair.hom_ext
      exact (congrArg ψ (P.lift_X _ hX)).trans hψroot
    exact (AlgEquiv.ofAlgHom (P.lift _ hX) ψ h1 h2).bijective

theorem isStandardEtale (n : ℕ) (u : R) (hn0 : n ≠ 0) (hn : IsUnit (n : R)) (hu : IsUnit u) :
    Algebra.IsStandardEtale R (AdjoinRoot (X ^ n - C u : R[X])) :=
  ⟨⟨kummerPresentation n u hn0 hn hu⟩⟩

end KummerEtaleSol

open KummerEtaleSol in
theorem _root_.AdjoinRoot.etale_and_finite_X_pow_sub_C_of_isUnit
    {R : Type u} [CommRing R] (n : ℕ) (u : R) (hn : IsUnit (n : R)) (hu : IsUnit u) :
    Algebra.Etale R (AdjoinRoot (X ^ n - C u : R[X])) ∧
      Module.Finite R (AdjoinRoot (X ^ n - C u : R[X])) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton (AdjoinRoot (X ^ n - C u : R[X])) :=
      (algebraMap R (AdjoinRoot (X ^ n - C u : R[X]))).codomain_trivial
    refine ⟨?_, ?_⟩
    · exact Algebra.Etale.of_equiv
        ((AlgEquiv.ofBijective (Algebra.ofId R (AdjoinRoot (X ^ n - C u : R[X])))
          ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩))
    · exact Module.Finite.of_surjective (Algebra.linearMap R _)
        (fun y => ⟨0, Subsingleton.elim _ _⟩)
  · have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    have : Algebra.IsStandardEtale R (AdjoinRoot (X ^ n - C u : R[X])) :=
      isStandardEtale n u hn0 hn hu
    exact ⟨inferInstance, (monic_X_pow_sub_C u hn0).finite_adjoinRoot⟩
end AlgebraicCurves.Foundations.FieldTheory.Proofs.AdjoinRoot_etale_and_finite_X_pow_sub_C_of_isUnit
end ProofImplementation
