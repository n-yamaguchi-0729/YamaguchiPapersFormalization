/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_pair_forall_ord_add_eq_zero_of_subset_riemannRochSpace.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.SplitIfs
import AlgebraicCurves.Cohomology.Adelic.Repartitions

/-!
# Exists pair forall ord add eq zero of subset riemann Roch Space
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsPairAllOrdAddZeroSubsetRR

open Submodule AlgebraicCurve in
theorem _root_.AlgebraicCurve.exists_pair_forall_ord_add_eq_zero_of_subset_riemannRochSpace
    {K F : Type*} [Field K] [Infinite K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasPrincipalDivisors K F]
    (D : AlgebraicCurve.Divisor K F) (V : Submodule K F) [FiniteDimensional K ↥V]
    (hVD : V ≤ AlgebraicCurve.riemannRochSpace D)
    (hbpf : ∀ w : AlgebraicCurve.Place K F, ∃ f ∈ V, f ≠ 0 ∧ w.ord f + D w = 0) :
    ∃ f₁ ∈ V, ∃ f₂ ∈ V, ∀ w : AlgebraicCurve.Place K F,
      (f₁ ≠ 0 ∧ w.ord f₁ + D w = 0) ∨ (f₂ ≠ 0 ∧ w.ord f₂ + D w = 0) := by
  classical
  rcases isEmpty_or_nonempty (Place K F) with hE | ⟨⟨w₀⟩⟩
  · exact ⟨0, V.zero_mem, 0, V.zero_mem, fun w => (hE.false w).elim⟩
  obtain ⟨f₁, hf₁V, hf₁0, -⟩ := hbpf w₀
  obtain ⟨P, hP⟩ := HasPrincipalDivisors.exists_divisor (K := K) f₁ hf₁0
  let bad : Finset (Place K F) := (P.support ∪ D.support).filter fun w => w.ord f₁ + D w ≠ 0
  have hbad : ∀ w, w.ord f₁ + D w ≠ 0 → w ∈ bad := by
    intro w hw
    refine Finset.mem_filter.mpr ⟨?_, hw⟩
    rw [Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff]
    by_contra h
    push Not at h
    apply hw
    rw [← hP.1 w, h.1, h.2, add_zero]
  let p : ↥bad → Submodule K ↥V := fun w =>
    (riemannRochSpace (D - Finsupp.single (w : Place K F) 1)).comap V.subtype
  have hp : ∀ w, p w ≠ ⊤ := by
    intro w htop
    obtain ⟨f, hfV, hf0, hford⟩ := hbpf w
    have hf : (⟨f, hfV⟩ : ↥V) ∈ p w := by rw [htop]; trivial
    have hf' := (mem_riemannRochSpace_iff.mp hf (w : Place K F)).resolve_left hf0
    rw [Finsupp.sub_apply, Finsupp.single_eq_same] at hf'
    change -(D (w : Place K F) - 1) ≤ (w : Place K F).ord f at hf'
    linarith
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨f₁, hf₁V, (x : F), x.2, fun w => ?_⟩
  by_cases hw : w.ord f₁ + D w = 0
  · exact Or.inl ⟨hf₁0, hw⟩
  · right
    have hxw := hx ⟨w, hbad w hw⟩
    have hx0 : (x : F) ≠ 0 := by
      intro h0
      apply hxw
      change (V.subtype x) ∈ riemannRochSpace _
      rw [show V.subtype x = (x : F) from rfl, h0]
      exact Submodule.zero_mem _
    refine ⟨hx0, ?_⟩
    have hxD := (mem_riemannRochSpace_iff.mp (hVD x.2) w).resolve_left hx0
    by_contra hne
    apply hxw
    change (x : F) ∈ riemannRochSpace (D - Finsupp.single w 1)
    rw [mem_riemannRochSpace_iff]
    intro w'
    right
    rw [Finsupp.sub_apply, Finsupp.single_apply]
    split_ifs with hww
    · subst hww; omega
    · rw [sub_zero]; exact (mem_riemannRochSpace_iff.mp (hVD x.2) w').resolve_left hx0
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsPairAllOrdAddZeroSubsetRR
end ProofImplementation
