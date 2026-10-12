/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_exists_mk_eq_forall_notMem_support.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Place_exists_forall_ord_eq_finset
import Nyll.AlgebraicCurves.Divisors.ClassGroup

/-!
Approximation of valuations moves a degree-zero divisor class away from finitely many places.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_exists_mk_eq_forall_notMem_support


noncomputable section

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace WC1bSolMV

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_mk_eq_forall_notMem [HasPrincipalDivisors K F]
    (x : Pic0 K F) (S : Finset (Place K F)) :
    ∃ D : Divisor.degZero (K := K) (F := F),
      Pic0.mk D = x ∧ ∀ v ∈ (D : Divisor K F).support, v ∉ S := by
  classical
  obtain ⟨D₀, hD₀⟩ := Pic0.mk_surjective x
  obtain ⟨g, hg0, hgord⟩ :=
    AlgebraicCurve.Place.exists_forall_ord_eq_finset (K := K) S (fun v => (D₀ : Divisor K F) v)
  obtain ⟨E, hEord, hEdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) g hg0
  set E' : Divisor.degZero (K := K) (F := F) := ⟨E, Divisor.mem_degZero.mpr hEdeg⟩ with hE'
  have hEprin : E' ∈ (Divisor.principal (K := K) (F := F)).addSubgroupOf
      (Divisor.degZero (K := K) (F := F)) := by
    rw [AddSubgroup.mem_addSubgroupOf]
    exact Divisor.mem_principal.mpr ⟨g, hg0, fun v => hEord v⟩
  refine ⟨D₀ - E', ?_, ?_⟩
  · have hmkE : Pic0.mk E' = 0 := (QuotientAddGroup.eq_zero_iff E').mpr hEprin
    change QuotientAddGroup.mk (D₀ - E') = x
    rw [QuotientAddGroup.mk_sub, ← hD₀]
    change Pic0.mk D₀ - Pic0.mk E' = Pic0.mk D₀
    rw [hmkE, sub_zero]
  · intro v hv hvS
    refine (Finsupp.mem_support_iff.mp hv) ?_
    change (D₀ : Divisor K F) v - E v = 0
    rw [hEord v, hgord v hvS, sub_self]

end WC1bSolMV

end AlgebraicCurve

open _root_.AlgebraicCurve in
open JacobianVarieties.Pic0.Proofs.Pic0_exists_mk_eq_forall_notMem_support.AlgebraicCurve in
theorem _root_.AlgebraicCurve.Pic0.exists_mk_eq_forall_notMem_support
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (x : Pic0 K F) (S : Finset (Place K F)) :
    ∃ D : Divisor.degZero (K := K) (F := F),
      Pic0.mk D = x ∧ ∀ v ∈ (D : Divisor K F).support, v ∉ S :=
  AlgebraicCurve.WC1bSolMV.exists_mk_eq_forall_notMem x S

end
end JacobianVarieties.Pic0.Proofs.Pic0_exists_mk_eq_forall_notMem_support
end ProofImplementation
