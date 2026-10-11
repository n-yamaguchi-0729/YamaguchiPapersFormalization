/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ProjSpaceCech_GradedModule_exists_forall_H_zero_shift_eq_sec_mk_of_isFG.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwist
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Nyll.AlgebraicCurves.Cohomology.Cech.ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one
import Nyll.AlgebraicCurves.Cohomology.Cech.ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk
import Nyll.AlgebraicCurves.Cohomology.Cech.ProjSpaceCech_GradedModule_subsingleton_cohomology_shift_of_isFG
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCech_GradedModule_Presentation_ker_isFG

/-!
# Proj Space Cech Graded Module exists forall H zero shift eq sec mk of is FG
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs
namespace ProjSpaceCech_GradedModule_exists_forall_H_zero_shift_eq_sec_mk_of_isFG

universe u

theorem _root_.ProjSpaceCech.GradedModule.exists_forall_H_zero_shift_eq_sec_mk_of_isFG
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (D : ProjSpaceCech.GradedModule R n) (hD : ProjSpaceCech.GradedModule.IsFG D) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      ∀ c : ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift D d) 0,
        ∃ m : D.M, m ∈ D.grade d ∧
          ∃ hm : m ∈ (ProjSpaceCech.GradedModule.shift D d).grade (∑ j : Fin (n + 1), (((0 : Fin (n
            + 1) → ℕ) j : ℕ) : ℤ)),
            ∀ s : ProjSpaceCech.Idx n 0,
              (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d (ProjSpaceCech.GradedModule.shift
                D d) 0)) from c).1 s =
                ProjSpaceCech.GradedModule.sec.mk (ProjSpaceCech.GradedModule.shift D d)
                  (ProjSpaceCech.Idx.img n s)
                  ⟨0, fun _ _ => rfl, m, hm⟩ := by
  obtain ⟨σ⟩ := hD
  obtain ⟨dK, hdK⟩ := ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG σ.ker
    (ProjSpaceCech.GradedModule.Presentation.ker_isFG σ)
  obtain ⟨d₁, hd₁⟩ := ProjSpaceCech.GradedModule.exists_forall_H_zero_pi_FD_shift_eq_sec_mk R n σ.d₀
  refine ⟨max dK d₁, fun d hd c => ?_⟩
  exact ProjSpaceCech.GradedModule.Presentation.forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one
    σ d
    (hdK d ((le_max_left _ _).trans hd) 1 le_rfl) (hd₁ d ((le_max_right _ _).trans hd)) c
end ProjSpaceCech_GradedModule_exists_forall_H_zero_shift_eq_sec_mk_of_isFG
end AlgebraicCurves.Cohomology.Cech.Proofs
end ProofImplementation
