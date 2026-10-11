/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Ext

/-!
# Linear Map nonempty ker Mod Range equiv of equiv comm
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace LinearMap_nonempty_kerModRange_equiv_of_equiv_comm

universe u v w

namespace LinearMap
open _root_.LinearMap
open _root_.LinearMap

section KerModRange

variable {R : Type u} [CommRing R] {C : ℕ → Type v} {C' : ℕ → Type w}
  [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, AddCommGroup (C' i)] [∀ i, Module R (C' i)]
  (d : ∀ i, C i →ₗ[R] C (i + 1)) (d' : ∀ i, C' i →ₗ[R] C' (i + 1))
  (e : ∀ i, C i ≃ₗ[R] C' i) (he : ∀ i x, e (i + 1) (d i x) = d' i (e i x))

include he

theorem kerModRange_map_ker (i : ℕ) :
    (LinearMap.ker (d i)).map (e i : C i →ₗ[R] C' i) = LinearMap.ker (d' i) := by
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← he, hx, map_zero]
  · intro hy
    refine ⟨(e i).symm y, ?_, by simp⟩
    apply (e (i + 1)).injective
    rw [he, LinearEquiv.apply_symm_apply, hy, map_zero]

/-- The kernel equivalence induced by a commuting family of componentwise linear equivalences. -/
def kerEquivOfComm (i : ℕ) : LinearMap.ker (d i) ≃ₗ[R] LinearMap.ker (d' i) :=
  ((e i).submoduleMap (LinearMap.ker (d i))).trans (LinearEquiv.ofEq _ _ (kerModRange_map_ker d d'
    e he i))

theorem kerEquivOfComm_apply (i : ℕ) (x : LinearMap.ker (d i)) :
    ((kerEquivOfComm d d' e he i x : LinearMap.ker (d' i)) : C' i) = e i x := rfl

theorem kerModRange_map_comap (i : ℕ) :
    ((LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype).map
        (kerEquivOfComm d d' e he (i + 1) : LinearMap.ker (d (i + 1)) →ₗ[R] LinearMap.ker (d' (i +
          1)))
      = (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i + 1))).subtype := by
  ext y
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range,
    LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, ⟨w, hw⟩, rfl⟩
    refine ⟨e i w, ?_⟩
    rw [kerEquivOfComm_apply, ← he, hw]
  · rintro ⟨w, hw⟩
    refine ⟨(kerEquivOfComm d d' e he (i + 1)).symm y, ⟨(e i).symm w, ?_⟩, by simp⟩
    have h1 : ((kerEquivOfComm d d' e he (i + 1)).symm y : C (i + 1))
        = (e (i + 1)).symm (y : C' (i + 1)) := by
      apply (e (i + 1)).injective
      rw [LinearEquiv.apply_symm_apply, ← kerEquivOfComm_apply d d' e he,
        LinearEquiv.apply_symm_apply]
    rw [h1]
    apply (e (i + 1)).injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hw]

theorem nonempty_kerModRange_equiv_of_equiv_comm' :
    Nonempty (LinearMap.ker (d 0) ≃ₗ[R] LinearMap.ker (d' 0)) ∧
    ∀ i, Nonempty
      ((LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i +
        1))).subtype) ≃ₗ[R]
       (LinearMap.ker (d' (i + 1)) ⧸ (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i +
         1))).subtype)) :=
  ⟨⟨kerEquivOfComm d d' e he 0⟩, fun i =>
    ⟨Submodule.Quotient.equiv _ _ (kerEquivOfComm d d' e he (i + 1)) (kerModRange_map_comap d d' e
      he i)⟩⟩

end KerModRange

end LinearMap

theorem _root_.LinearMap.nonempty_kerModRange_equiv_of_equiv_comm
    {R : Type u} [CommRing R] {C C' : ℕ → Type u}
    [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, AddCommGroup (C' i)] [∀ i, Module R (C'
      i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (d' : ∀ i, C' i →ₗ[R] C' (i + 1))
    (e : ∀ i, C i ≃ₗ[R] C' i) (he : ∀ i x, e (i + 1) (d i x) = d' i (e i x)) :
    Nonempty (LinearMap.ker (d 0) ≃ₗ[R] LinearMap.ker (d' 0)) ∧
    ∀ i, Nonempty
      ((LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i +
        1))).subtype) ≃ₗ[R]
       (LinearMap.ker (d' (i + 1)) ⧸ (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i +
         1))).subtype)) :=
  LinearMap.nonempty_kerModRange_equiv_of_equiv_comm' d d' e he
end AlgebraicCurves.Foundations.Algebra.Proofs.LinearMap_nonempty_kerModRange_equiv_of_equiv_comm
end ProofImplementation
