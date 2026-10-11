/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Cohomology.RiemannRoch.FiniteDimensional_lSpace
import AlgebraicCurves.Cohomology.RiemannRoch.RiemannGenusReachedAt_eq_of_ge
import AlgebraicCurves.Cohomology.AdeleSpace_eq_of_genusReached
import AlgebraicCurves.Geometry.One_le_deg
import AlgebraicCurves.Cohomology.RiemannRoch.Ell_add_of_forall_eq_ord

/-!
Approximation with a prescribed valuation bound from a place where the Riemann genus is reached.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs
namespace Exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

theorem strongApprox_aux {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (S : Set (Place K F)) {v₀ : Place K F} (hv₀ : v₀ ∉ S) (D : Divisor K F)
    (α : Place K F → F) (hα : {v | ¬ v.adicValuation (α v) ≤ WithZero.exp (D v)}.Finite) :
    ∃ f : F, ∀ v ∈ S, v.adicValuation (α v - f) ≤ WithZero.exp (D v) := by
  classical
  have : Nonempty (Place K F) := ⟨v₀⟩
  have hαA : α ∈ adeleSpace K F := by
    set T : Finset (Place K F) := hα.toFinset with hT
    have hmemT : ∀ v, v ∈ T ↔ ¬ v.adicValuation (α v) ≤ WithZero.exp (D v) := fun v => by
      rw [hT, Set.Finite.mem_toFinset]; rfl
    set c : ℕ := T.sup fun v => (-(v.ord (α v)) - D v).toNat with hc
    have hcv : ∀ v ∈ T, -(v.ord (α v)) - D v ≤ (c : ℤ) := by
      intro v hv
      have h1 : (-(v.ord (α v)) - D v).toNat ≤ c :=
        Finset.le_sup (f := fun v => (-(v.ord (α v)) - D v).toNat) hv
      have h2 : ((-(v.ord (α v)) - D v).toNat : ℤ) ≤ (c : ℤ) := by exact_mod_cast h1
      omega
    let E : Divisor K F := D + T.sum fun w => (c : ℤ) • Finsupp.single w 1
    have hE : ∀ v, E v = D v + if v ∈ T then (c : ℤ) else 0 := by
      intro v
      simp only [E, Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
        Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
    refine adeleBdd_le_adeleSpace (D := E) (fun v => ?_)
    by_cases hv : v ∈ T
    · have hbad := (hmemT v).mp hv
      have hα0 : α v ≠ 0 := fun h0 => hbad (by rw [h0]; simp)
      rw [v.adicValuation_eq_exp_neg_ord hα0, WithZero.exp_le_exp, hE, ite_eq_left hv]
      have := hcv v hv
      omega
    · have hok : v.adicValuation (α v) ≤ WithZero.exp (D v) := by
        by_contra h'
        exact hv ((hmemT v).mpr h')
      refine hok.trans ?_
      rw [WithZero.exp_le_exp, hE, ite_eq_right hv, add_zero]
  have hdeg₀ : (1 : ℤ) ≤ v₀.deg := by exact_mod_cast one_le_deg (K := K) v₀
  set N : Divisor K F := D ⊓ 0 with hN
  set m : ℕ := (γ + Divisor.degree D₀ - Divisor.degree N).toNat with hm
  have hm' : γ + Divisor.degree D₀ - Divisor.degree N ≤ (m : ℤ) := by
    rw [hm]; exact Int.self_le_toNat _
  set W : Divisor K F := (m : ℤ) • Finsupp.single v₀ 1 + N with hW
  have hWdeg : Divisor.degree W = (m : ℤ) * v₀.deg + Divisor.degree N := by
    rw [hW, map_add, map_zsmul, Divisor.degree_single, one_mul, smul_eq_mul]
  have hWv : ∀ v ∈ S, W v ≤ D v := by
    intro v hv
    have hne : v ≠ v₀ := fun h => hv₀ (h ▸ hv)
    have hs : (Finsupp.single v₀ (1 : ℤ)) v = 0 := by simp [hne]
    rw [hW, Finsupp.add_apply, Finsupp.smul_apply, hs, smul_zero, zero_add, hN, Finsupp.inf_apply]
    exact inf_le_left
  set A : Divisor K F := W - D₀ with hA
  have hAdeg : γ ≤ Divisor.degree A := by
    rw [hA, map_sub, hWdeg]
    have : (m : ℤ) ≤ (m : ℤ) * v₀.deg := by nlinarith
    omega
  have hellA : 0 < ell A := by
    have := h.isMax A
    omega
  have : Nontrivial ↥(LSpace A) := Module.nontrivial_of_finrank_pos hellA
  obtain ⟨⟨z, hzA⟩, hz0'⟩ := exists_ne (0 : ↥(LSpace A))
  have hz0 : z ≠ 0 := fun h0 => hz0' (Subtype.ext h0)
  obtain ⟨P, hP, hPdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) z hz0
  have hzord : ∀ v, -A v ≤ v.ord z := ((mem_lSpace_iff_ord).mp hzA).resolve_left hz0
  have hD₀le : D₀ ≤ W + P := by
    intro v
    have h1 := hzord v
    rw [hA, Finsupp.sub_apply] at h1
    rw [Finsupp.add_apply, hP v]
    omega
  have hreach' := h.eq_of_ge hD₀le
  have hellWP : ell (W + P) = ell W := ell_add_of_forall_eq_ord W hz0 hP
  have hdegWP : Divisor.degree (W + P) = Divisor.degree W := by rw [map_add, hPdeg, add_zero]
  have hreachW : RiemannGenusReachedAt γ W :=
    ⟨finiteDimensional_lSpace (K := K) (F := F) W, by rw [← hdegWP, ← hellWP]; exact hreach',
      h.isMax⟩
  have hSA := adeleSpace_eq_of_genusReached hreachW
  rw [hSA, Submodule.mem_sup] at hαA
  obtain ⟨a, ha, g, hg, hag⟩ := hαA
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp hg
  refine ⟨f, fun v hv => ?_⟩
  have hav : α v - f = a v := by
    have := congrFun hag v
    rw [Pi.add_apply, diagonalHom_apply] at this
    rw [← this]; ring
  rw [hav]
  exact ((mem_adeleBdd.mp ha) v).trans (WithZero.exp_le_exp.mpr (hWv v hv))

end AlgebraicCurve

open _root_.AlgebraicCurves.Cohomology.RiemannRoch.Proofs in
open _root_.AlgebraicCurve
  Exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt.AlgebraicCurve in
theorem _root_.AlgebraicCurve.exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt {K F :
    Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (S : Set (Place K F)) {v₀ : Place K F} (hv₀ : v₀ ∉ S) (D : Divisor K F)
    (α : Place K F → F) (hα : {v | v ∈ S ∧ ¬ v.adicValuation (α v) ≤ WithZero.exp (D v)}.Finite) :
    ∃ f : F, ∀ v ∈ S, v.adicValuation (α v - f) ≤ WithZero.exp (D v) := by
  classical
  set α' : Place K F → F := fun v => if v ∈ S then α v else 0 with hα'
  have hα'fin : {v : Place K F | ¬ v.adicValuation (α' v) ≤ WithZero.exp (D v)}.Finite := by
    refine hα.subset ?_
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    by_cases hvS : v ∈ S
    · simp only [hα', ite_eq_left hvS] at hv
      exact ⟨hvS, hv⟩
    · simp only [hα', ite_eq_right hvS] at hv
      exact absurd (by simp) hv
  obtain ⟨f, hf⟩ := strongApprox_aux h S hv₀ D α' hα'fin
  refine ⟨f, fun v hv => ?_⟩
  have := hf v hv
  simp only [hα', ite_eq_left hv] at this
  exact this
end Exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs
end ProofImplementation
