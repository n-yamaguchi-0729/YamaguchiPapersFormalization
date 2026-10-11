/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_mem_of_forall_exists_X_pow_mul_mem_of_forall_mem_iff_app_awayToSection_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.Tactic.Ring.RingNF
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.AlgebraicCurves.Hilbert.Functor.Basic
import Nyll.AlgebraicCurves.Foundations.Algebra.Nat_MacaulayPow

/-!
# mem of forall exists X pow mul mem of forall mem iff app away To Section eq zero
-/

section ProofImplementation

namespace AlgebraicGeometry.HilbertFunctor

open _root_.MvPolynomial _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
  AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem mem_of_forall_exists_X_pow_mul_mem_of_forall_mem_iff_app_awayToSection_eq_zero
    (n : ℕ) (k : Type) [Field k]
    (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hZ : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
          (F ∈ I ↔ ∀ i : Fin (n + 1),
            (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
              (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })) = 0))
    (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d)
    (hsat : ∀ i : Fin (n + 1), ∃ N : ℕ, MvPolynomial.X i ^ N * F ∈ I) :
    F ∈ I := by
  rw [hZ d F hF]
  intro i
  obtain ⟨N, hN⟩ := hsat i
  have hG : (X i ^ N * F).IsHomogeneous (N + d) := (MvPolynomial.isHomogeneous_X_pow i N).mul hF
  have h := (hZ (N + d) (X i ^ N * F) hG).mp hN i
  have heq : (HomogeneousLocalization.mk
      { deg := N + d
        num := ⟨X i ^ N * F, (MvPolynomial.mem_homogeneousSubmodule (N + d) _).mpr hG⟩
        den := ⟨MvPolynomial.X i ^ (N + d), (MvPolynomial.mem_homogeneousSubmodule (N + d) _).mpr
          (MvPolynomial.isHomogeneous_X_pow i (N + d))⟩
        den_mem := ⟨N + d, rfl⟩ } : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule
          (Fin (n + 1)) k) (X i))
      = (HomogeneousLocalization.mk
      { deg := d
        num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
        den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
          (MvPolynomial.isHomogeneous_X_pow i d)⟩
        den_mem := ⟨d, rfl⟩ } : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule
          (Fin (n + 1)) k) (X i)) := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; ring⟩
  rw [← heq]
  exact h
end AlgebraicGeometry.HilbertFunctor
end ProofImplementation
