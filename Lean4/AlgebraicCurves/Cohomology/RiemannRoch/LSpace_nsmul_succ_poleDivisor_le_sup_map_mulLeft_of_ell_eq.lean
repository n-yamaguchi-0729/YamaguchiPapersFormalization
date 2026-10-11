/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Cohomology.RiemannRoch.Mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor

/-!
# LSpace nsmul succ pole Divisor le sup map mul Left of ell eq
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.LSpaceNsmulSuccPoleDivisorLeSup

open AlgebraicCurve

theorem _root_.AlgebraicCurve.lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)))
    (M₀ d g₀ : ℕ)
    (hell : ∀ N, M₀ ≤ N → (ell (N • D) : ℤ) = N * d + 1 - g₀)
    (m : ℕ) (hm : M₀ + 1 ≤ m) :
    (LSpace ((m + 1) • D) : Submodule K F)
      ≤ LSpace (m • D) ⊔ (LSpace (m • D)).map (LinearMap.mulLeft K x) := by
  set φ : F →ₗ[K] F := LinearMap.mulLeft K x with hφdef
  rcases eq_or_ne x 0 with hx0 | hx0
  · intro g hg
    refine Submodule.mem_sup_left
      ((mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor x D hD m).2 g hg ?_)
    simp [hx0]
  have hφinj : Function.Injective φ := fun a b h =>
    mul_left_cancel₀ hx0 (by simpa [hφdef, LinearMap.mulLeft_apply] using h)
  obtain ⟨hsh1m, _⟩ := mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor x D hD m
  have hm1 : m - 1 + 1 = m := by omega
  obtain ⟨hsh1p, hsh2p⟩ := mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor x D hD (m - 1)
  rw [hm1] at hsh1p hsh2p
  have hD0 : 0 ≤ D := fun v => by simp [hD v]
  have hmono : ∀ {a b : ℕ}, a ≤ b → (LSpace (a • D) : Submodule K F) ≤ LSpace (b • D) := by
    intro a b hab
    refine lSpace_mono ?_
    intro v
    have : a • (D v) ≤ b • (D v) := nsmul_le_nsmul_left (hD0 v) hab
    simpa using this
  have hW_le : (LSpace (m • D) : Submodule K F) ⊔ (LSpace (m • D)).map φ ≤ LSpace ((m + 1) • D) :=
    sup_le (hmono m.le_succ)
      (Submodule.map_le_iff_le_comap.2 fun g hg => hsh1m g hg)
  have := hFD m; have := hFD (m + 1); have := hFD (m - 1)
  have : FiniteDimensional K ↥((LSpace (m • D) : Submodule K F).map φ) :=
    (Submodule.equivMapOfInjective φ hφinj _).symm.finiteDimensional
  have hinf : (LSpace (m • D) : Submodule K F) ⊓ (LSpace (m • D)).map φ
            = (LSpace ((m - 1) • D)).map φ := by
    apply le_antisymm
    · rintro z ⟨hzVm, g, hgVm, rfl⟩
      exact ⟨g, hsh2p g hgVm hzVm, rfl⟩
    · rintro z ⟨g, hgVp, rfl⟩
      exact ⟨hsh1p g hgVp, g, hmono (Nat.sub_le _ _) hgVp, rfl⟩
  have hfr_map : ∀ (V : Submodule K F), FiniteDimensional K ↥V →
      Module.finrank K ↥(V.map φ) = Module.finrank K ↥V := fun V _ =>
    (Submodule.equivMapOfInjective φ hφinj V).symm.finrank_eq
  have h1m : 1 ≤ m := by omega
  have hfr_m  : (Module.finrank K ↥(LSpace (m • D) : Submodule K F) : ℤ) = m * d + 1 - g₀ :=
    by have := hell m (by omega); exact_mod_cast this
  have hfr_m1 : (Module.finrank K ↥(LSpace ((m + 1) • D) : Submodule K F) : ℤ)
              = (m + 1) * d + 1 - g₀ :=
    by have := hell (m + 1) (by omega); exact_mod_cast this
  have hfr_p  : (Module.finrank K ↥(LSpace ((m - 1) • D) : Submodule K F) : ℤ)
              = (m - 1 : ℕ) * d + 1 - g₀ :=
    by have := hell (m - 1) (by omega); exact_mod_cast this
  have hsi := Submodule.finrank_sup_add_finrank_inf_eq
    (LSpace (m • D) : Submodule K F) ((LSpace (m • D)).map φ)
  rw [hinf] at hsi
  have hfr_W : (Module.finrank K ↥((LSpace (m • D) : Submodule K F) ⊔ (LSpace (m • D)).map φ) : ℤ)
             = Module.finrank K ↥(LSpace ((m + 1) • D) : Submodule K F) := by
    rw [hfr_map _ (hFD (m - 1)), hfr_map _ (hFD m)] at hsi
    have hsiZ : (Module.finrank K ↥((LSpace (m • D) : Submodule K F) ⊔ (LSpace (m • D)).map φ) : ℤ)
              + Module.finrank K ↥(LSpace ((m - 1) • D) : Submodule K F)
              = Module.finrank K ↥(LSpace (m • D) : Submodule K F)
              + Module.finrank K ↥(LSpace (m • D) : Submodule K F) := by
      exact_mod_cast hsi
    have hmnat : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
      have : ((m - 1 : ℕ) : ℤ) + 1 = (m : ℤ) := by exact_mod_cast hm1
      linarith
    have hpZ : ((m - 1 : ℕ) : ℤ) * d = (m : ℤ) * d - d := by
      rw [hmnat]; ring
    rw [hfr_m1]
    have h1 := hfr_m; have h2 := hfr_p
    rw [hpZ] at h2
    linarith [h1, h2, hsiZ]
  have heq := Submodule.eq_of_le_of_finrank_le hW_le (by exact_mod_cast hfr_W.ge)
  exact heq.ge
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.LSpaceNsmulSuccPoleDivisorLeSup
end ProofImplementation
