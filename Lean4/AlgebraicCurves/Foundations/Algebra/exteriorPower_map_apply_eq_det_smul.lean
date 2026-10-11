/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_exteriorPower_map_apply_eq_det_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Data.Fintype.EquivFin
import AlgebraicCurves.Foundations.Algebra.exteriorPower_iotaMulti_comp_eq_det_smul

/-!
# exterior Power map apply eq det smul
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.exteriorPower_map_apply_eq_det_smul

theorem _root_.exteriorPower.map_apply_eq_det_smul {A : Type*} [CommRing A] {M : Type*}
  [AddCommGroup M]
    [Module A M] {ι : Type*} [Fintype ι] (b : Module.Basis ι A M) {n : ℕ} (hn : Fintype.card ι = n)
    (f : M →ₗ[A] M) (x : ⋀[A]^n M) :
    exteriorPower.map n f x = LinearMap.det f • x := by
  classical
  let b' : Module.Basis (Fin n) A M := b.reindex (Fintype.equivFinOfCardEq hn)
  have hgen : ∀ m : Fin n → M,
      exteriorPower.map n f (exteriorPower.ιMulti A n m) = LinearMap.det f • exteriorPower.ιMulti A
        n m := by
    intro m
    rw [exteriorPower.map_apply_ιMulti]
    exact exteriorPower.iotaMulti_comp_eq_det_smul b' f m
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨m, rfl⟩ := hy; exact hgen m
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, smul_add]
  | smul r y _ hy => rw [map_smul, hy, smul_comm]
end AlgebraicCurves.Foundations.Algebra.Proofs.exteriorPower_map_apply_eq_det_smul
end ProofImplementation
