/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_finset_forall_norm_appLE_sub_lt_imp_false_of_ne_of_isSeparated.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Algebra.Monoid
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import AlgebraicCurves.Geometry.Schemes.exists_sum_appLE_mul_appLE_ne_zero_and_forall_eq_zero_of_ne_of_isSeparated

/-!
# exists finset forall norm app LE sub lt imp false of ne of is Separated
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace exists_finset_forall_norm_appLE_sub_lt_imp_false_of_ne_of_isSeparated

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

open Filter

theorem
  _root_.AlgebraicGeometry.exists_finset_forall_norm_appLE_sub_lt_imp_false_of_ne_of_isSeparated
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} [IsSeparated f]
    (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hxy : x ≠ y) :
    ∃ (U V : G.Opens) (hx : ⊤ ≤ x.1 ⁻¹ᵁ U) (hy : ⊤ ≤ y.1 ⁻¹ᵁ V)
      (fsU : Finset (Γ(G, U))) (fsV : Finset (Γ(G, V))) (ε : ℝ), 0 < ε ∧
      ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hPU : ⊤ ≤ P.1 ⁻¹ᵁ U) (hPV : ⊤ ≤ P.1
        ⁻¹ᵁ V),
        (∀ φ ∈ fsU, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hPU) φ) -
            (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((x.1.appLE U ⊤ hx) φ)‖ < ε) →
        (∀ ψ ∈ fsV, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE V ⊤ hPV) ψ) -
            (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((y.1.appLE V ⊤ hy) ψ)‖ < ε) → False := by
  classical
  obtain ⟨U, V, hx, hy, n, a, b, hne, hzero⟩ :=
    AlgebraicGeometry.exists_sum_appLE_mul_appLE_ne_zero_and_forall_eq_zero_of_ne_of_isSeparated x
    y hxy
  set α : Fin n → ℂ := fun i => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((x.1.appLE U ⊤ hx) (a i))
    with hα
  set β : Fin n → ℂ := fun i => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((y.1.appLE V ⊤ hy) (b i))
    with hβ
  have hne' : ∑ i : Fin n, α i * β i ≠ 0 := hne
  have hcont : ContinuousAt (fun p : (Fin n → ℂ) × (Fin n → ℂ) => ∑ i : Fin n, p.1 i * p.2 i) (α,
    β) :=
    (continuous_finsetSum _ fun i _ => ((continuous_apply i).comp continuous_fst).mul
      ((continuous_apply i).comp continuous_snd)).continuousAt
  have hopen : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
  have hmem : (fun p : (Fin n → ℂ) × (Fin n → ℂ) => ∑ i : Fin n, p.1 i * p.2 i) (α, β) ∈ {z : ℂ | z
    ≠ 0} := hne'
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hcont.preimage_mem_nhds (hopen.mem_nhds hmem))
  refine ⟨U, V, hx, hy, Finset.univ.image a, Finset.univ.image b, ε, hε, ?_⟩
  intro P hPU hPV hU hV
  set s : Fin n → ℂ := fun i => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hPU) (a
    i)) with hs
  set t : Fin n → ℂ := fun i => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE V ⊤ hPV) (b
    i)) with ht
  have hst : ((s, t) : (Fin n → ℂ) × (Fin n → ℂ)) ∈ Metric.ball (α, β) ε := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · rw [dist_pi_lt_iff hε]; intro i; rw [dist_eq_norm]; exact hU (a i) (Finset.mem_image_of_mem _
        (Finset.mem_univ i))
    · rw [dist_pi_lt_iff hε]; intro i; rw [dist_eq_norm]; exact hV (b i) (Finset.mem_image_of_mem _
        (Finset.mem_univ i))
  have h := hball hst
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at h
  exact h (hzero P hPU hPV)
end exists_finset_forall_norm_appLE_sub_lt_imp_false_of_ne_of_isSeparated
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
