/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Push
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomial_finrank_piece_succ_le_macaulayPow
import Nyll.AlgebraicCurves.Foundations.Algebra.Nat_macaulayPow_lt_macaulayPow_of_lt
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.AlgebraicCurves.Hilbert.Functor.Basic
import Nyll.AlgebraicCurves.Foundations.Algebra.Nat_MacaulayPow

/-!
# Mv Polynomial le finrank piece of forall succ eq macaulay Pow of eventually eq
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Polynomial.Proofs
namespace MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GotzmannB29

theorem lt_of_lt {n : ℕ} {K : Type} [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (H : ℕ → ℕ) (g : ℕ) (hg : 1 ≤ g) (hH : ∀ e, g ≤ e → H (e + 1) = Nat.macaulayPow e (H e))
    (d : ℕ) (hd : g ≤ d) (hlt : Module.finrank K (piece J d) < H d) :
    ∀ e, d ≤ e → Module.finrank K (piece J e) < H e := by
  intro e hde
  induction e with
  | zero =>
    obtain rfl : d = 0 := by omega
    exact hlt
  | succ e ih =>
    rcases Nat.lt_or_ge e d with h | h
    · obtain rfl : d = e + 1 := by omega
      exact hlt
    · calc Module.finrank K (piece J (e + 1)) ≤ Nat.macaulayPow e (Module.finrank K (piece J e)) :=
            MvPolynomial.finrank_piece_succ_le_macaulayPow n e (by omega) K J hJ
        _ < Nat.macaulayPow e (H e) := Nat.macaulayPow_lt_macaulayPow_of_lt (by omega) (ih h)
        _ = H (e + 1) := (hH e (by omega)).symm

theorem le_finrank_piece {n : ℕ} {K : Type} [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (H : ℕ → ℕ) (g : ℕ) (hg : 1 ≤ g) (hH : ∀ e, g ≤ e → H (e + 1) = Nat.macaulayPow e (H e))
    (hev : ∃ D₀ : ℕ, ∀ e, D₀ ≤ e → Module.finrank K (piece J e) = H e)
    (d : ℕ) (hd : g ≤ d) : H d ≤ Module.finrank K (piece J d) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨D₀, hD₀⟩ := hev
  have := lt_of_lt J hJ H g hg hH d hd hlt (max d D₀) (le_max_left _ _)
  rw [hD₀ _ (le_max_right _ _)] at this
  exact lt_irrefl _ this

end GotzmannB29

open GotzmannB29 in
theorem _root_.MvPolynomial.le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq
    (n g : ℕ) (hg : 1 ≤ g) (H : ℕ → ℕ)
    (hH : ∀ e : ℕ, g ≤ e → H (e + 1) = Nat.macaulayPow e (H e))
    (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (hev : ∃ D : ℕ, ∀ e : ℕ, D ≤ e → Module.finrank K (piece J e) = H e) :
    ∀ d : ℕ, g ≤ d → H d ≤ Module.finrank K (piece J d) := by
  intro d hd
  exact GotzmannB29.le_finrank_piece J hJ H g hg hH hev d hd
end MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq
end AlgebraicCurves.Foundations.Polynomial.Proofs
end ProofImplementation
