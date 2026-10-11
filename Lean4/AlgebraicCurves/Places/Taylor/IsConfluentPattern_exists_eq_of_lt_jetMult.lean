/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_IsConfluentPattern_exists_eq_of_lt_jetMult.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Places.Taylor

/-!
# Is Confluent Pattern exists eq of lt jet Mult
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Taylor.Proofs.IsConfluentPattern_exists_eq_of_lt_jetMult

open AlgebraicCurve

theorem _root_.AlgebraicCurve.IsConfluentPattern.exists_eq_of_lt_jetMult
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {M : ℕ} {P : Fin M → Place K F} {t : Fin M → F} {e : Fin M → ℕ}
    (hpat : IsConfluentPattern P t e) (i : Fin M) {q : ℕ} (hq : q < jetMult P (P i)) :
    ∃ i', P i' = P i ∧ e i' = q := by
  classical
  obtain ⟨-, h2, h3⟩ := hpat
  set B : Finset (Fin M) := Finset.univ.filter (fun i' => P i' = P i) with hB
  have hcard : B.card = jetMult P (P i) := by
    rw [hB]; unfold AlgebraicCurve.jetMult; convert rfl
  have hmaps : ∀ a (ha : a ∈ B), (fun a (_ : a ∈ B) => e a) a ha ∈ Finset.range (jetMult P (P i))
    := by
    intro a ha
    have hPa : P a = P i := (Finset.mem_filter.mp ha).2
    rw [Finset.mem_range, ← hPa]; exact h3 a
  have hinj : ∀ a₁ a₂ (h₁ : a₁ ∈ B) (h₂ : a₂ ∈ B),
      (fun a (_ : a ∈ B) => e a) a₁ h₁ = (fun a (_ : a ∈ B) => e a) a₂ h₂ → a₁ = a₂ :=
    fun a₁ a₂ h₁ h₂ he =>
      h2 a₁ a₂ (((Finset.mem_filter.mp h₁).2).trans ((Finset.mem_filter.mp h₂).2).symm) he
  obtain ⟨a, ha, hqa⟩ := Finset.surj_on_of_inj_on_of_card_le (fun a (_ : a ∈ B) => e a) hmaps hinj
    (by rw [Finset.card_range, hcard]) q (Finset.mem_range.mpr hq)
  exact ⟨a, (Finset.mem_filter.mp ha).2, hqa.symm⟩
end AlgebraicCurves.Places.Taylor.Proofs.IsConfluentPattern_exists_eq_of_lt_jetMult
end ProofImplementation
