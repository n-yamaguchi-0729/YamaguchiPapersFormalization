/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_DoubleComplex_exists_HTot_equiv_of_levelwise_equiv_pinned.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Quotient.Basic
import SchemeTheory.Cohomology.Sheaves.DoubleComplex

/-!
# Double Complex exists HTot equiv of levelwise equiv pinned
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.HomologicalAlgebra.Proofs
namespace DoubleComplex_exists_HTot_equiv_of_levelwise_equiv_pinned

universe u

namespace KBPSOL

open DoubleComplex

theorem main
    {R : Type u} [CommRing R] (D D' : DoubleComplex.Bounded R)
    (e : ∀ p q : ℕ, D.C p q ≃ₗ[R] D'.C p q)
    (hH : ∀ (p q : ℕ) (x : D.C p q), e (p + 1) q (D.dH p q x) = D'.dH p q (e p q x))
    (hV : ∀ (p q : ℕ) (x : D.C p q), e p (q + 1) (D.dV p q x) = D'.dV p q (e p q x))
    (n : ℕ) :
    ∃ E : DoubleComplex.HTot D n ≃ₗ[R] DoubleComplex.HTot D' n,
      ∀ c : ↥(LinearMap.ker (DoubleComplex.dTot D n)),
        ∃ hc : (fun i : DoubleComplex.Diag n => e i.1.1 i.1.2 (c.1 i)) ∈ LinearMap.ker
          (DoubleComplex.dTot D' n),
          E (Submodule.Quotient.mk c) = Submodule.Quotient.mk ⟨_, hc⟩ := by
  classical
  let T : ∀ m : ℕ, Tot D m ≃ₗ[R] Tot D' m := fun m =>
    LinearEquiv.piCongrRight (fun i : Diag m => e i.1.1 i.1.2)
  have hTapp : ∀ (m : ℕ) (c : Tot D m) (i : Diag m), T m c i = e i.1.1 i.1.2 (c i) := fun m c i =>
    rfl
  have hT : ∀ (m : ℕ) (c : Tot D m), dTot D' m (T m c) = T (m + 1) (dTot D m c) := by
    intro m c
    funext i
    obtain ⟨⟨pp, qq⟩, h⟩ := i
    rw [hTapp]
    match pp, qq, h with
    | 0, 0, h => exact absurd h (by omega)
    | 0, q' + 1, h =>
      rw [dTot_apply_zero_succ, dTot_apply_zero_succ, hTapp, hV]
    | p' + 1, 0, h =>
      rw [dTot_apply_succ_zero, dTot_apply_succ_zero, hTapp, hH]
    | p' + 1, q' + 1, h =>
      rw [dTot_apply_succ_succ, dTot_apply_succ_succ, hTapp, hTapp, map_add, map_zsmul, hH, hV]
  have hmapker : ∀ m : ℕ, (LinearMap.ker (dTot D m)).map (T m : Tot D m →ₗ[R] Tot D' m) =
      LinearMap.ker (dTot D' m) := by
    intro m
    ext y
    rw [Submodule.mem_map, LinearMap.mem_ker]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [LinearMap.mem_ker] at hc
      rw [LinearEquiv.coe_coe, hT, hc, map_zero]
    · intro hy
      refine ⟨(T m).symm y, ?_, LinearEquiv.apply_symm_apply _ _⟩
      rw [LinearMap.mem_ker]
      apply (T (m + 1)).injective
      rw [← hT, LinearEquiv.apply_symm_apply, hy, map_zero]
  let K : ∀ m : ℕ, LinearMap.ker (dTot D m) ≃ₗ[R] LinearMap.ker (dTot D' m) := fun m =>
    LinearEquiv.ofSubmodules (T m) _ _ (hmapker m)
  have hKval : ∀ (m : ℕ) (x : LinearMap.ker (dTot D m)), ((K m x : LinearMap.ker (dTot D' m)) : Tot
    D' m) =
      T m (x : Tot D m) := fun m x => rfl
  have hmapB : (HTotB D n).map (K n : LinearMap.ker (dTot D n) →ₗ[R] LinearMap.ker (dTot D' n)) =
      HTotB D' n := by
    match n with
    | 0 => exact Submodule.map_bot _
    | n' + 1 =>
      ext y
      simp only [HTotB, Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply,
        LinearMap.mem_range]
      constructor
      · rintro ⟨x, ⟨c, hc⟩, rfl⟩
        refine ⟨T n' c, ?_⟩
        rw [LinearEquiv.coe_coe, hKval, ← hc, hT]
      · rintro ⟨c', hc'⟩
        have hx : T (n' + 1) (dTot D n' ((T n').symm c')) = (y : Tot D' (n' + 1)) := by
          rw [← hT, LinearEquiv.apply_symm_apply, hc']
        refine ⟨⟨dTot D n' ((T n').symm c'), ?_⟩, ⟨(T n').symm c', rfl⟩, ?_⟩
        · rw [LinearMap.mem_ker, ← LinearMap.comp_apply, dTot_comp_dTot, LinearMap.zero_apply]
        · apply Subtype.ext
          rw [LinearEquiv.coe_coe, hKval]
          exact hx
  refine ⟨Submodule.Quotient.equiv (HTotB D n) (HTotB D' n) (K n) hmapB, fun c => ?_⟩
  have hc : (fun i : Diag n => e i.1.1 i.1.2 (c.1 i)) ∈ LinearMap.ker (dTot D' n) := (K n c).2
  refine ⟨hc, ?_⟩
  rfl

end KBPSOL

theorem _root_.DoubleComplex.exists_HTot_equiv_of_levelwise_equiv_pinned
    {R : Type u} [CommRing R] (D D' : DoubleComplex.Bounded R)
    (e : ∀ p q : ℕ, D.C p q ≃ₗ[R] D'.C p q)
    (hH : ∀ (p q : ℕ) (x : D.C p q), e (p + 1) q (D.dH p q x) = D'.dH p q (e p q x))
    (hV : ∀ (p q : ℕ) (x : D.C p q), e p (q + 1) (D.dV p q x) = D'.dV p q (e p q x))
    (n : ℕ) :
    ∃ E : DoubleComplex.HTot D n ≃ₗ[R] DoubleComplex.HTot D' n,
      ∀ c : ↥(LinearMap.ker (DoubleComplex.dTot D n)),
        ∃ hc : (fun i : DoubleComplex.Diag n => e i.1.1 i.1.2 (c.1 i)) ∈ LinearMap.ker
          (DoubleComplex.dTot D' n),
          E (Submodule.Quotient.mk c) = Submodule.Quotient.mk ⟨_, hc⟩ :=
  KBPSOL.main D D' e hH hV n
end DoubleComplex_exists_HTot_equiv_of_levelwise_equiv_pinned
end AlgebraicCurves.Foundations.HomologicalAlgebra.Proofs
end ProofImplementation
