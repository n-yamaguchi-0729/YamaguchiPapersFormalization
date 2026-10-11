/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_exists_eq_pow_and_eq_ord_of_inv_smul_D_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Differentials.PthPowerKernel

/-!
# Divisor exists eq pow and eq ord of inv smul D eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_exists_eq_pow_and_eq_ord_of_inv_smul_D_eq_zero

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve

namespace DlogRecipeKer

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isSeparable_expansionField [PerfectField K] (p : ℕ) [Fact p.Prime] [CharP K p] [CharP F p]
    (t : F) (hsepK : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F) (x : F) :
    IsSeparable (KwPke.kw_pke_expansionField (ℓ := p) t).toSubfield x := by
  set L₂ := (KwPke.kw_pke_expansionField (ℓ := p) t).toSubfield with hL₂
  set L₁ := (IntermediateField.adjoin K ({t} : Set F)).toSubfield with hL₁
  have hle : L₁ ≤ L₂ := by
    rw [hL₁, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro y (⟨c, rfl⟩ | hy)
    · have := PerfectField.toPerfectRing (K := K) p
      have hc : algebraMap K F c = (algebraMap K F ((frobeniusEquiv K p).symm c)) ^ p := by
        rw [← map_pow, ← frobenius_def, frobenius_apply_frobeniusEquiv_symm]
      rw [hc]
      exact (KwPke.kw_pke_expansionField (ℓ := p) t).algebraMap_mem
        ⟨_, (KwPke.kw_pke_mem_pthPowers_iff F p).mpr ⟨_, rfl⟩⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact IntermediateField.mem_adjoin_simple_self _ y
  have h1 : IsSeparable L₁ x := by
    have : IsSeparable (IntermediateField.adjoin K ({t} : Set F)) x :=
      Algebra.IsSeparable.isSeparable _ x
    exact this
  let : Algebra L₁ L₂ := (Subfield.inclusion hle).toAlgebra
  have : IsScalarTower L₁ L₂ F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact IsSeparable.tower_top L₂ h1

theorem exists_eq_pow_and_eq_ord_of_dlog_eq_zero [PerfectField K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (t : F) (hsepK : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F)
    (hdt : D K F t ≠ 0) {D₀ : Divisor K F} {f : F} (hf : f ≠ 0)
    (hD : ∀ v : Place K F, (p : ℤ) * D₀ v = v.ord f) (h0 : f⁻¹ • D K F f = 0) :
    ∃ g : F, g ≠ 0 ∧ f = g ^ p ∧ ∀ v : Place K F, D₀ v = v.ord g := by
  have : CharP F p := (algebraMap K F).charP_iff_charP p |>.mp inferInstance
  have hdf : D K F f = 0 := by
    rwa [smul_eq_zero, or_iff_right (inv_ne_zero hf)] at h0
  obtain ⟨g, rfl⟩ := KwPke.kw_pke_ker_d_pthPower (K := K) t
    (isSeparable_expansionField p t hsepK) hdt hdf
  have hg : g ≠ 0 := fun h => hf (by rw [h, zero_pow (Fact.out : p.Prime).ne_zero])
  refine ⟨g, hg, rfl, fun v => ?_⟩
  have h := hD v
  rw [← zpow_natCast, v.ord_zpow] at h
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h

end DlogRecipeKer

end AlgebraicCurve

end

theorem _root_.AlgebraicCurve.Divisor.exists_eq_pow_and_eq_ord_of_inv_smul_D_eq_zero
    (K F : Type*) [Field K] [Field F] [Algebra K F] [PerfectField K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (t : F) (hsepK : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F)
    (hdt : KaehlerDifferential.D K F t ≠ 0)
    (D : AlgebraicCurve.Divisor K F) (f : F) (hf : f ≠ 0)
    (hD : ∀ v : AlgebraicCurve.Place K F, (p : ℤ) * D v = v.ord f)
    (h0 : f⁻¹ • KaehlerDifferential.D K F f = 0) :
    ∃ g : F, g ≠ 0 ∧ f = g ^ p ∧ ∀ v : AlgebraicCurve.Place K F, D v = v.ord g :=
  AlgebraicCurve.DlogRecipeKer.exists_eq_pow_and_eq_ord_of_dlog_eq_zero p t hsepK hdt hf hD h0
end AlgebraicCurves.Divisors.Proofs.Divisor_exists_eq_pow_and_eq_ord_of_inv_smul_D_eq_zero
end ProofImplementation
