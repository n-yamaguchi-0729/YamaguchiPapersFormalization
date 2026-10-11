/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_TwoChartCech_Sections_nonempty_linearEquiv_H0_and_H1_of_linearEquiv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech

/-!
# Two Chart Cech Sections nonempty linear Equiv H0 and H1 of linear Equiv
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartSectionsEquivH0H1Equiv

universe u v v' w w'

open TwoChartCech

theorem _root_.TwoChartCech.Sections.nonempty_linearEquiv_H0_and_H1_of_linearEquiv
    {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R} {𝒰' : Cover.{u, v'} R}
    (S : Sections.{u, v, w} 𝒰) (S' : Sections.{u, v', w'} 𝒰')
    (e₀ : S.M0 ≃ₗ[R] S'.M0) (e₁ : S.M1 ≃ₗ[R] S'.M1) (e₀₁ : S.M01 ≃ₗ[R] S'.M01)
    (h₀ : ∀ m : S.M0, e₀₁ (S.r0 m) = S'.r0 (e₀ m)) (h₁ : ∀ m : S.M1, e₀₁ (S.r1 m) = S'.r1 (e₁ m)) :
    (Nonempty (↥S.H0 ≃ₗ[R] ↥S'.H0) ∧ Nonempty (S.H1 ≃ₗ[R] S'.H1)) ∧
      Module.finrank R ↥S.H0 = Module.finrank R ↥S'.H0 ∧ (Subsingleton S.H1 ↔ Subsingleton S'.H1)
        := by
  let E : (S.M0 × S.M1) ≃ₗ[R] (S'.M0 × S'.M1) := e₀.prodCongr e₁
  have hE : ∀ s, S'.cechDiff (E s) = e₀₁ (S.cechDiff s) := by
    rintro ⟨a, b⟩
    simp only [E, LinearEquiv.prodCongr_apply, Sections.cechDiff_apply, map_sub, h₀, h₁]
  have hker : Submodule.map (E : (S.M0 × S.M1) →ₗ[R] (S'.M0 × S'.M1)) S.H0 = S'.H0 := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' : S.cechDiff s = 0 := hs
      change S'.cechDiff (E s) = 0
      rw [hE, hs', map_zero]
    · intro hy
      have hy' : S'.cechDiff y = 0 := hy
      refine ⟨E.symm y, ?_, by simp⟩
      change S.cechDiff (E.symm y) = 0
      apply e₀₁.injective
      rw [← hE, LinearEquiv.apply_symm_apply, hy', map_zero]
  let f0 : ↥S.H0 ≃ₗ[R] ↥S'.H0 := (E.submoduleMap S.H0).trans (LinearEquiv.ofEq _ _ hker)
  have hran : Submodule.map (e₀₁ : S.M01 →ₗ[R] S'.M01) (LinearMap.range S.cechDiff) =
    LinearMap.range S'.cechDiff := by
    ext y
    constructor
    · rintro ⟨z, ⟨s, rfl⟩, rfl⟩
      exact ⟨E s, by rw [LinearEquiv.coe_coe, ← hE]⟩
    · rintro ⟨s, rfl⟩
      exact ⟨S.cechDiff (E.symm s), ⟨_, rfl⟩,
        by rw [LinearEquiv.coe_coe, ← hE, LinearEquiv.apply_symm_apply]⟩
  let f1 : S.H1 ≃ₗ[R] S'.H1 := Submodule.Quotient.equiv _ _ e₀₁ hran
  refine ⟨⟨⟨f0⟩, ⟨f1⟩⟩, f0.finrank_eq, ?_⟩
  exact ⟨fun h => f1.symm.toEquiv.subsingleton, fun h => f1.toEquiv.subsingleton⟩
end AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartSectionsEquivH0H1Equiv
end ProofImplementation
