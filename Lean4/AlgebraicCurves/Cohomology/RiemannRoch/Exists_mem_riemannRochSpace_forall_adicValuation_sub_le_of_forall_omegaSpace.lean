/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_mem_riemannRochSpace_forall_adicValuation_sub_le_of_forall_omegaSpace.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Cohomology.Adelic.Index

/-!
# Exists mem riemann Roch Space forall adic Valuation sub le of forall omega Space
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsMemRRSpaceAllAdicValuation

open WithZero

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Theta1Sol
open _root_.AlgebraicCurve

open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem single_sum_apply_of_mem (T : Finset (Place K F)) {v : Place K F} (hv : v ∈ T) :
    (∑ x ∈ T, Finsupp.single x (1 : ℤ)) v = 1 := by
  classical
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply]
  simp [hv]

theorem single_sum_apply_of_not_mem (T : Finset (Place K F)) {v : Place K F} (hv : v ∉ T) :
    (∑ x ∈ T, Finsupp.single x (1 : ℤ)) v = 0 := by
  classical
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply]
  simp [hv]

end AlgebraicCurve.Theta1Sol

open _root_.AlgebraicCurve AlgebraicCurve in
theorem
  _root_.AlgebraicCurve.exists_mem_riemannRochSpace_forall_adicValuation_sub_le_of_forall_omegaSpace
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : AlgebraicCurve.Divisor K F) (T : Finset (AlgebraicCurve.Place K F)) (g :
      AlgebraicCurve.Place K F → F)
    (hg : ∀ x ∈ T, x.adicValuation (g x) ≤ exp (D x))
    (r : ↥(AlgebraicCurve.adeleSpace K F))
    (hrT : ∀ v ∈ T, (r : AlgebraicCurve.Place K F → F) v = g v) (hr0 : ∀ v ∉ T, (r :
      AlgebraicCurve.Place K F → F) v = 0)
    (horth : ∀ μ ∈ AlgebraicCurve.omegaSpace (K := K) (F := F) (D - ∑ x ∈ T, Finsupp.single x 1),
      μ r = 0) :
    ∃ f ∈ AlgebraicCurve.riemannRochSpace (K := K) (F := F) D,
      ∀ x ∈ T, x.adicValuation (f - g x) ≤ exp (D x - 1) := by
  classical
  set E : Divisor K F := ∑ x ∈ T, Finsupp.single x 1 with hE
  have hmem : r ∈ adeleBddPrincipal K F (D - E) := by
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := adeleBddPrincipal K F (D - E)),
      Submodule.mem_dualCoannihilator]
    intro μ hμ
    exact horth μ hμ
  rw [adeleBddPrincipal, Submodule.mem_sup] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  rw [Submodule.mem_comap] at ha hb
  obtain ⟨f, hf⟩ := hb
  have hcoord : ∀ v : Place K F, (r : Place K F → F) v = (a : Place K F → F) v + f := by
    intro v
    have := congrArg (fun z : ↥(adeleSpace K F) => (z : Place K F → F) v) hab
    simp only [Submodule.coe_add, Pi.add_apply] at this
    have hbv : (b : Place K F → F) v = f := by
      have h2 := congrFun hf v
      rw [diagonalHom_apply] at h2
      exact h2.symm
    rw [← this, hbv]
  have haBdd : ∀ v : Place K F, v.adicValuation ((a : Place K F → F) v) ≤ exp ((D - E) v) := ha
  have hEv1 : ∀ v ∈ T, E v = 1 := fun v hv =>
    by rw [hE]; exact AlgebraicCurve.Theta1Sol.single_sum_apply_of_mem T hv
  have hEv0 : ∀ v ∉ T, E v = 0 := fun v hv =>
    by rw [hE]; exact AlgebraicCurve.Theta1Sol.single_sum_apply_of_not_mem T hv
  refine ⟨f, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ T
    · have e : f = g v - (a : Place K F → F) v := by
        have := hcoord v; rw [hrT v hv] at this; rw [this]; ring
      rw [e]
      refine le_trans (Valuation.map_sub _ _ _) (max_le (hg v hv) ?_)
      refine le_trans (haBdd v) ?_
      rw [Finsupp.sub_apply, hEv1 v hv]
      exact WithZero.exp_le_exp.mpr (by omega)
    · have e : f = -(a : Place K F → F) v := by
        have := hcoord v; rw [hr0 v hv] at this
        exact (neg_eq_of_add_eq_zero_right this.symm).symm
      rw [e, Valuation.map_neg]
      refine le_trans (haBdd v) ?_
      rw [Finsupp.sub_apply, hEv0 v hv, sub_zero]
  · intro x hx
    have e : f - g x = -(a : Place K F → F) x := by
      have := hcoord x; rw [hrT x hx] at this; rw [this]; ring
    rw [e, Valuation.map_neg]
    refine le_trans (haBdd x) ?_
    rw [Finsupp.sub_apply, hEv1 x hx]

end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsMemRRSpaceAllAdicValuation
end ProofImplementation
