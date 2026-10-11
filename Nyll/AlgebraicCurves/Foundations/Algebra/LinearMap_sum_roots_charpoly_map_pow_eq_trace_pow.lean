/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_LinearMap_sum_roots_charpoly_map_pow_eq_trace_pow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Tactic.SimpRw

/-!
# Linear Map sum roots charpoly map pow eq trace pow
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace LinearMap_sum_roots_charpoly_map_pow_eq_trace_pow

namespace P2mC2H1

open Polynomial Module

section algClosed

variable {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]

theorem trace_pow_restrict_maxGenEigenspace (S : Module.End E W) (μ : E) (n : ℕ) :
    LinearMap.trace E _ ((S ^ n).restrict
      (S.mapsTo_maxGenEigenspace_of_comm (Commute.refl S |>.pow_right n) μ)) =
      μ ^ n * (finrank E (S.maxGenEigenspace μ) : E) := by
  have hS : Set.MapsTo S ↑(S.maxGenEigenspace μ) ↑(S.maxGenEigenspace μ) :=
    S.mapsTo_maxGenEigenspace_of_comm (Commute.refl S) μ
  set Sμ : Module.End E (S.maxGenEigenspace μ) := S.restrict hS with hSμ
  have hnil := S.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
  have hpow : ∀ k : ℕ, (S ^ k).restrict
      (S.mapsTo_maxGenEigenspace_of_comm (Commute.refl S |>.pow_right k) μ) = Sμ ^ k := by
    intro k
    exact (Module.End.pow_restrict (f' := S) k hS
      (h' := S.mapsTo_maxGenEigenspace_of_comm (Commute.refl S |>.pow_right k) μ)).symm
  rw [hpow n]
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, one_mul, LinearMap.trace_one]
  | succ k ih =>
    have hcomm : Commute (Sμ ^ k) Sμ := (Commute.refl Sμ).pow_left k
    have hk : Sμ ^ (k + 1) = (Sμ ^ k) ∘ₗ Sμ := by rw [pow_succ]; rfl
    rw [hk, LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ hcomm hnil, ih, ← mul_assoc,
      ← pow_succ']

theorem sum_roots_pow_eq_trace_pow [IsAlgClosed E] (S : Module.End E W) (n : ℕ) :
    ((S.charpoly).roots.map (fun z => z ^ n)).sum = LinearMap.trace E W (S ^ n) := by
  classical
  have hind := S.independent_maxGenEigenspace
  have htop := S.iSup_maxGenEigenspace_eq_top
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have h_fin : {μ : E | S.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  have hf : ∀ μ : E, Set.MapsTo (S ^ n) ↑(S.maxGenEigenspace μ) ↑(S.maxGenEigenspace μ) :=
    fun μ => S.mapsTo_maxGenEigenspace_of_comm (Commute.refl S |>.pow_right n) μ
  rw [LinearMap.trace_eq_sum_trace_restrict' hds h_fin hf]
  simp_rw [trace_pow_restrict_maxGenEigenspace]
  rw [Finset.sum_multiset_map_count]
  have hset : S.charpoly.roots.toFinset = h_fin.toFinset := by
    ext μ
    rw [Multiset.mem_toFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
      mem_roots (S.charpoly_monic).ne_zero, ne_eq, ← Submodule.finrank_eq_zero,
      LinearMap.finrank_maxGenEigenspace_eq, ← ne_eq, ← Nat.pos_iff_ne_zero, rootMultiplicity_pos']
    exact ⟨fun h => ⟨(S.charpoly_monic).ne_zero, h⟩, fun h => h.2⟩
  rw [hset]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [count_roots, ← LinearMap.finrank_maxGenEigenspace_eq, nsmul_eq_mul, mul_comm]

end algClosed

theorem sum_roots_charpoly_map_pow_eq_trace_pow {L : Type*} [Field L] {V : Type*} [AddCommGroup V]
    [Module L V] [FiniteDimensional L V] (E : Type*) [Field E] [Algebra L E] [IsAlgClosed E]
    (T : V →ₗ[L] V) (n : ℕ) :
    (((T.charpoly).map (algebraMap L E)).roots.map (fun z => z ^ n)).sum =
      algebraMap L E (LinearMap.trace L V (T ^ n)) := by
  rw [← LinearMap.charpoly_baseChange, sum_roots_pow_eq_trace_pow, ← LinearMap.baseChange_pow,
    LinearMap.trace_baseChange]

end P2mC2H1

theorem _root_.LinearMap.sum_roots_charpoly_map_pow_eq_trace_pow {L : Type*} [Field L] {V : Type*}
    [AddCommGroup V] [Module L V] [FiniteDimensional L V] (E : Type*) [Field E] [Algebra L E]
    [IsAlgClosed E] (T : V →ₗ[L] V) (n : ℕ) :
    (((T.charpoly).map (algebraMap L E)).roots.map (fun z => z ^ n)).sum =
      algebraMap L E (LinearMap.trace L V (T ^ n)) :=
  P2mC2H1.sum_roots_charpoly_map_pow_eq_trace_pow E T n
end AlgebraicCurves.Foundations.Algebra.Proofs.LinearMap_sum_roots_charpoly_map_pow_eq_trace_pow
end ProofImplementation
