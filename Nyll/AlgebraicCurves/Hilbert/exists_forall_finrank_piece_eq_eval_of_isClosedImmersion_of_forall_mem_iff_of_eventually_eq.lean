/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.NormCast
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ext
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.AlgebraicCurves.Hilbert.Functor.Basic
import Nyll.AlgebraicCurves.Foundations.Algebra.Nat_MacaulayPow
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomial_finrank_piece_succ_le_macaulayPow
import Nyll.AlgebraicCurves.Foundations.Algebra.Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp
import Nyll.AlgebraicCurves.Hilbert.mem_of_forall_exists_X_pow_mul_mem_of_forall_mem_iff_app_awayToSection_eq_zero
import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomial_exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem

/-!
# exists forall finrank piece eq eval of is Closed Immersion of forall mem iff of eventually
eq
-/

section ProofImplementation

open _root_.AlgebraicGeometry.HilbertFunctor (
  mem_of_forall_exists_X_pow_mul_mem_of_forall_mem_iff_app_awayToSection_eq_zero)

namespace AlgebraicCurves.Hilbert.Proofs.HilbertPolynomialRanks

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GotzReg

/-- A polynomial realized eventually by the dimensions of a homogeneous quotient. -/
def IsHilbPoly (n : ℕ) (P : Polynomial ℚ) : Prop :=
  ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
    (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
    ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)

theorem exists_gotz (n : ℕ) (P : Polynomial ℚ) (hP : IsHilbPoly n P) :
    ∃ g : ℕ, 1 ≤ g ∧ ∃ H : ℕ → ℕ, (∀ e : ℕ, g ≤ e → (H e : ℚ) = P.eval (e : ℚ)) ∧
      (∀ e : ℕ, g ≤ e → H (e + 1) = Nat.macaulayPow e (H e)) := by
  obtain ⟨K, _, I, hI, d₁, hd₁⟩ := hP
  obtain ⟨D₀, hD₀⟩ := Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
    (fun e => Module.finrank K (piece I e)) 1 le_rfl
    (fun d hd => MvPolynomial.finrank_piece_succ_le_macaulayPow n d hd K I hI)
  refine ⟨max (max d₁ D₀) 1, le_max_right _ _, fun e => Module.finrank K (piece I e), ?_, ?_⟩
  · intro e he
    exact hd₁ e (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) he)
  · intro e he
    exact hD₀ e (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) he)

open Classical in
/-- A positive Gotzmann bound for a realizable Hilbert polynomial, and zero otherwise. -/
def gnum (n : ℕ) (P : Polynomial ℚ) : ℕ :=
  if h : IsHilbPoly n P then (exists_gotz n P h).choose else 0

theorem gnum_eq (n : ℕ) (P : Polynomial ℚ) (h : IsHilbPoly n P) : gnum n P = (exists_gotz n P
  h).choose := by
  classical
  unfold gnum
  rw [dite_eq_left h]

variable {n : ℕ}

theorem isHomogeneous_of_forall {K : Type} [CommRing K] (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : ∀ p ∈ I, ∀ i : ℕ, homogeneousComponent i p ∈ I) :
    I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) := by
  intro i p hp
  rw [show ((DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) K) p i : MvPolynomial (Fin (n
    + 1)) K))
      = homogeneousComponent i p from decomposition.decompose'_apply p i]
  exact hI p hp i

theorem forall_of_isHomogeneous {K : Type} [CommRing K] (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K)) :
    ∀ p ∈ I, ∀ i : ℕ, homogeneousComponent i p ∈ I := by
  intro p hp i
  have := hI i hp
  rw [show ((DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) K) p i : MvPolynomial (Fin (n
    + 1)) K))
      = homogeneousComponent i p from decomposition.decompose'_apply p i] at this
  exact this

theorem homogeneous_sup_span_singleton {K : Type} [CommRing K] (I : Ideal (MvPolynomial (Fin (n +
  1)) K))
    (hI : ∀ p ∈ I, ∀ i : ℕ, homogeneousComponent i p ∈ I)
    (ℓ : MvPolynomial (Fin (n + 1)) K) {e : ℕ} (hℓ : ℓ.IsHomogeneous e) :
    ∀ p ∈ I ⊔ Ideal.span {ℓ}, ∀ i : ℕ, homogeneousComponent i p ∈ I ⊔ Ideal.span {ℓ} := by
  apply forall_of_isHomogeneous
  apply Ideal.IsHomogeneous.sup (isHomogeneous_of_forall I hI)
  apply Ideal.homogeneous_span
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨e, (mem_homogeneousSubmodule e _).mpr hℓ⟩

end GotzReg
end
end AlgebraicCurves.Hilbert.Proofs.HilbertPolynomialRanks

namespace AlgebraicGeometry.HilbertFunctor
noncomputable section

open _root_.AlgebraicCurves.Hilbert.Proofs.HilbertPolynomialRanks
open _root_.MvPolynomial _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
  _root_.AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra


open GotzReg in
theorem exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq
    (n : ℕ) (P : Polynomial ℚ) :
    ∃ G : ℕ, ∀ (k : Type) [Field k] [IsAlgClosed k]
      (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)),
        IsClosedImmersion ιk →
      ∀ (I : Ideal (MvPolynomial (Fin (n + 1)) k)),
        (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) →
        (∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
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
                    den_mem := ⟨d, rfl⟩ })) = 0)) →
        (∃ D₀ : ℕ, ∀ d : ℕ, D₀ ≤ d → (Module.finrank k (piece I d) : ℚ) = P.eval (d : ℚ)) →
        ∀ d : ℕ, G ≤ d → (Module.finrank k (piece I d) : ℚ) = P.eval (d : ℚ) := by
  classical
  set Q : Polynomial ℚ := P - P.comp (Polynomial.X - 1) with hQ
  refine ⟨max (gnum n P) (gnum n Q), ?_⟩
  intro k _ _ Zk ιk hι I hhom hZ hev d hd
  obtain ⟨D₁, hD₁⟩ := hev
  have hP : IsHilbPoly n P := ⟨k, inferInstance, I, hhom, D₁, hD₁⟩
  obtain ⟨hg1, H, hHP, hHmax⟩ := (exists_gotz n P hP).choose_spec
  rw [gnum_eq n P hP] at hd
  set g : ℕ := (exists_gotz n P hP).choose with hg
  have hevH : ∃ D : ℕ, ∀ e : ℕ, D ≤ e → Module.finrank k (piece I e) = H e := by
    refine ⟨max D₁ g, fun e he => ?_⟩
    have h1 := hD₁ e (le_trans (le_max_left _ _) he)
    have h2 := hHP e (le_trans (le_max_right _ _) he)
    exact_mod_cast h1.trans h2.symm
  have lo := MvPolynomial.le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq
    n g hg1 H hHmax k I hhom hevH
  have hsat : ∀ (e : ℕ) (F : MvPolynomial (Fin (n + 1)) k), F.IsHomogeneous e →
      (∀ i : Fin (n + 1), ∃ N : ℕ, MvPolynomial.X i ^ N * F ∈ I) → F ∈ I :=
    fun e F hF hs =>
      mem_of_forall_exists_X_pow_mul_mem_of_forall_mem_iff_app_awayToSection_eq_zero
        n k Zk ιk I hZ e F hF hs
  have : Infinite k := IsAlgClosed.instInfinite
  obtain ⟨a, hcolon⟩ :=
    MvPolynomial.exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem n k I hhom
      hsat
  set ℓ : MvPolynomial (Fin (n + 1)) k := ∑ i : Fin (n + 1), MvPolynomial.C (a i) * MvPolynomial.X
    i with hℓ
  have hℓ1 : ℓ.IsHomogeneous 1 := by
    apply IsHomogeneous.sum
    intro i _
    have := (isHomogeneous_C (Fin (n + 1)) (a i)).mul (isHomogeneous_X k i)
    simpa using this
  have ses :=
    MvPolynomial.finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp
    n k I hhom ℓ hℓ1 hcolon
  have hhom' := homogeneous_sup_span_singleton I hhom ℓ hℓ1
  have hQe : ∀ e : ℕ, Q.eval ((e + 1 : ℕ) : ℚ) = P.eval ((e + 1 : ℕ) : ℚ) - P.eval (e : ℚ) := by
    intro e
    simp only [hQ, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_X,
      Polynomial.eval_one,
      Nat.cast_succ, add_sub_cancel_right]
  have hQev : ∀ e : ℕ, D₁ + 1 ≤ e →
      (Module.finrank k (piece (I ⊔ Ideal.span {ℓ}) e) : ℚ) = Q.eval (e : ℚ) := by
    intro e he
    obtain ⟨e', rfl⟩ : ∃ e' : ℕ, e = e' + 1 := ⟨e - 1, by omega⟩
    have hs := ses e'
    have h1 := hD₁ (e' + 1) (by omega)
    have h0 := hD₁ e' (by omega)
    rw [hQe e', ← h1, ← h0]
    have : (Module.finrank k (piece (I ⊔ Ideal.span {ℓ}) (e' + 1)) : ℚ) + (Module.finrank k (piece
      I e') : ℚ)
        = (Module.finrank k (piece I (e' + 1)) : ℚ) := by exact_mod_cast hs
    linarith
  have hQ' : IsHilbPoly n Q := ⟨k, inferInstance, I ⊔ Ideal.span {ℓ}, hhom', D₁ + 1, hQev⟩
  obtain ⟨hg1', H', hH'P, hH'max⟩ := (exists_gotz n Q hQ').choose_spec
  rw [gnum_eq n Q hQ'] at hd
  set g' : ℕ := (exists_gotz n Q hQ').choose with hg'
  have hevH' : ∃ D : ℕ, ∀ e : ℕ, D ≤ e → Module.finrank k (piece (I ⊔ Ideal.span {ℓ}) e) = H' e :=
    by
    refine ⟨max (D₁ + 1) g', fun e he => ?_⟩
    have h1 := hQev e (le_trans (le_max_left _ _) he)
    have h2 := hH'P e (le_trans (le_max_right _ _) he)
    exact_mod_cast h1.trans h2.symm
  have lo' := MvPolynomial.le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq
    n g' hg1' H' hH'max k (I ⊔ Ideal.span {ℓ}) hhom' hevH'
  have step : ∀ e : ℕ, g' ≤ e + 1 →
      (Module.finrank k (piece I e) : ℚ) - P.eval (e : ℚ) ≤
        (Module.finrank k (piece I (e + 1)) : ℚ) - P.eval ((e + 1 : ℕ) : ℚ) := by
    intro e he
    have h := lo' (e + 1) he
    have hs := ses e
    have hH := hH'P (e + 1) he
    rw [hQe e] at hH
    have h' : (H' (e + 1) : ℚ) ≤ (Module.finrank k (piece (I ⊔ Ideal.span {ℓ}) (e + 1)) : ℚ) := by
      exact_mod_cast h
    have hs' : (Module.finrank k (piece (I ⊔ Ideal.span {ℓ}) (e + 1)) : ℚ) + (Module.finrank k
      (piece I e) : ℚ)
        = (Module.finrank k (piece I (e + 1)) : ℚ) := by exact_mod_cast hs
    linarith
  have key : ∀ j e : ℕ, g' ≤ e + 1 → D₁ ≤ e + j →
      (Module.finrank k (piece I e) : ℚ) - P.eval (e : ℚ) ≤ 0 := by
    intro j
    induction j with
    | zero =>
      intro e _ hD
      have := hD₁ e (by omega)
      linarith
    | succ j ih =>
      intro e he hD
      have h1 := step e he
      have h2 := ih (e + 1) (by omega) (by omega)
      linarith
  have hdg' : g' ≤ d := le_trans (le_max_right _ _) hd
  have up : (Module.finrank k (piece I d) : ℚ) - P.eval (d : ℚ) ≤ 0 :=
    key D₁ d (by omega) (by omega)
  have hlo := lo d (le_trans (le_max_left _ _) hd)
  have hHd := hHP d (le_trans (le_max_left _ _) hd)
  have hlo' : (H d : ℚ) ≤ (Module.finrank k (piece I d) : ℚ) := by exact_mod_cast hlo
  linarith
end
end AlgebraicGeometry.HilbertFunctor
end ProofImplementation
