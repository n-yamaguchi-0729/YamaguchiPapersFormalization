/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_divisor_forall_eq_weightFloor.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.FunctionFields.CurveOver

/-!
# Exists divisor forall eq weight Floor
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Exists_divisor_forall_eq_weightFloor

open AlgebraicCurve

namespace DivexG

theorem exists_divisor_ord (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] [IsCurveOver K
  F] (f : F) :
    ∃ D : Divisor K F, ∀ v : Place K F, D v = v.ord f := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨0, fun v => by simp⟩
  · have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
    obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf
    exact ⟨D, hD⟩

end DivexG

theorem _root_.AlgebraicCurve.exists_divisor_forall_eq_weightFloor
    (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F]
    (y : F) (m : ℕ) :
    ∃ D : AlgebraicCurve.Divisor K F, ∀ w : AlgebraicCurve.Place K F,
      D w = (if 0 < w.ord y then (2 * (m : ℤ) * w.ord y) / 3 else 0)
          + (if 0 < w.ord (y - 1728) then ((m : ℤ) * w.ord (y - 1728)) / 2 else 0)
          + (if w.ord y < 0 then (m : ℤ) * w.ord y else 0) := by
  classical
  obtain ⟨Dj, hDj⟩ := DivexG.exists_divisor_ord K y
  obtain ⟨Dc, hDc⟩ := DivexG.exists_divisor_ord K (y - 1728)
  let R : Place K F → ℤ := fun w =>
    (if 0 < w.ord y then (2 * (m : ℤ) * w.ord y) / 3 else 0)
      + (if 0 < w.ord (y - 1728) then ((m : ℤ) * w.ord (y - 1728)) / 2 else 0)
      + (if w.ord y < 0 then (m : ℤ) * w.ord y else 0)
  have hsupp : ∀ w, R w ≠ 0 → w ∈ Dj.support ∪ Dc.support := by
    intro w hw
    by_contra hmem
    rw [Finset.mem_union, not_or, Finsupp.mem_support_iff, Finsupp.mem_support_iff, not_not,
      not_not,
      hDj w, hDc w] at hmem
    apply hw
    simp only [R, hmem.1, hmem.2, lt_irrefl, ite_false, add_zero]
  refine ⟨Finsupp.onFinset (Dj.support ∪ Dc.support) R hsupp, fun w => ?_⟩
  rw [Finsupp.onFinset_apply]

end AlgebraicCurves.Divisors.Proofs.Exists_divisor_forall_eq_weightFloor
end ProofImplementation
