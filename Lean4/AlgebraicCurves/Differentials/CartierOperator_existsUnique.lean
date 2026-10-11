/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_cartierOperator_existsUnique.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Differentials.CartierCoordinates
import AlgebraicCurves.Geometry.Exists_D_ne_zero
import AlgebraicCurves.Differentials.Kw_cart_C_pow_smul_D_eq_zero
import AlgebraicCurves.Differentials.Kw_cart_C_pow_pred_smul_D
import AlgebraicCurves.Places.PDigits_existsUnique
import AlgebraicCurves.FunctionFields.CurveOver

/-!
# Cartier Operator exists Unique
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.CartierOperator_existsUnique
attribute [-simp] AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero
  AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one

universe u v

open KaehlerDifferential AlgebraicCurve.KwPke AlgebraicCurve.KwCart

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace CartierOperatorConstruction
open _root_.AlgebraicCurve

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

variable (p : ℕ) [hp : Fact p.Prime] [CharP F p]

private theorem hsep_of_pDigits {t : F}
    (hdig : ∀ g : F, ∃ a : Fin p → F, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ)) :
    ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := p) t).toSubfield x := by
  intro x
  have hx : x ∈ kw_pke_expansionField (ℓ := p) t := by
    obtain ⟨a, rfl⟩ := hdig x
    refine sum_mem fun i _ => mul_mem ?_
      (pow_mem (IntermediateField.mem_adjoin_simple_self (kw_pke_pthPowers F p) t) _)
    have hmem : a i ^ p ∈ kw_pke_pthPowers F p :=
      (kw_pke_mem_pthPowers_iff F p).mpr ⟨a i, rfl⟩
    exact (kw_pke_expansionField (ℓ := p) t).algebraMap_mem ⟨a i ^ p, hmem⟩
  exact isSeparable_algebraMap
    (⟨x, (IntermediateField.mem_toSubfield _ x).mpr hx⟩ :
      (kw_pke_expansionField (ℓ := p) t).toSubfield)

private theorem exists_cartierOperator [IsCurveOver K F] {t : F} (hdt : D K F t ≠ 0)
    (hdig : ∀ g : F, ∃ a : Fin p → F, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ)) :
    ∃ C : Ω[F⁄K] →+ Ω[F⁄K],
      (∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω) ∧
      (∀ f : F, C (D K F f) = 0) ∧
      (∀ f : F, C (f ^ (p - 1) • D K F f) = D K F f) := by
  have hspan : Submodule.span F {D K F t} = ⊤ := kw_cart_hspan_of_isCurveOver hdt
  have hsep := hsep_of_pDigits p hdig
  have hdeg : (minpoly (kw_pke_pthPowers F p) t).natDegree = p :=
    kw_cart_minpoly_natDegree_eq hdt
  refine ⟨AddMonoidHom.mk' (kw_cart_C (K := K) t hdt hspan hsep hdeg)
    (kw_cart_C_add t hdt hspan hsep hdeg), ?_, ?_, ?_⟩
  · intro f ω
    exact kw_cart_C_semilinear t hdt hspan hsep hdeg f ω
  · intro f
    have h := kw_cart_C_pow_smul_D_eq_zero t hdt hspan hsep hdeg f (i := 0)
      (by have := hp.out.two_le; omega)
    rwa [pow_zero, one_smul] at h
  · intro f
    exact kw_cart_C_pow_pred_smul_D t hdt hspan hsep hdeg f

section Unique

variable (C : Ω[F⁄K] →+ Ω[F⁄K])
  (hC₁ : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
  (hC₂ : ∀ f : F, C (D K F f) = 0)
  (hC₃ : ∀ f : F, C (f ^ (p - 1) • D K F f) = D K F f)

include hC₁ hC₂ in
private theorem cartier_pow_smul_D_eq_zero (t : F) {i : ℕ} (hi : i + 1 < p) :
    C (t ^ i • D K F t) = 0 := by
  have hne : ((i + 1 : ℕ) : F) ≠ 0 := by
    intro h0
    have hdvd := (CharP.cast_eq_zero_iff F p (i + 1)).1 h0
    exact absurd (Nat.le_of_dvd (Nat.succ_pos i) hdvd) (not_le.2 hi)
  have hleib : D K F (t ^ (i + 1)) = ((i + 1 : ℕ) : F) • (t ^ i • D K F t) := by
    rw [(D K F).leibniz_pow t (i + 1), Nat.add_sub_cancel, Nat.cast_smul_eq_nsmul]
  have hcp : (((i + 1 : ℕ) : F)⁻¹) ^ p = ((i + 1 : ℕ) : F)⁻¹ := by
    rw [inv_pow, ← frobenius_def, map_natCast]
  have hrew : t ^ i • D K F t = (((i + 1 : ℕ) : F)⁻¹) ^ p • D K F (t ^ (i + 1)) := by
    rw [hcp, hleib, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hrew, hC₁, hC₂, smul_zero]
include hC₁ hC₂ hC₃ in
private theorem cartier_digits (t : F) (a : Fin p → F) :
    C ((∑ i : Fin p, a i ^ p * t ^ (i : ℕ)) • D K F t) =
      a ⟨p - 1, Nat.sub_lt hp.out.pos Nat.one_pos⟩ • D K F t := by
  rw [Finset.sum_smul, map_sum,
    Finset.sum_eq_single (⟨p - 1, Nat.sub_lt hp.out.pos Nat.one_pos⟩ : Fin p)]
  · rw [mul_smul, hC₁, hC₃]
  · intro i _ hi
    have hi' : (i : ℕ) ≠ p - 1 := fun h => hi (Fin.ext h)
    have hlt : (i : ℕ) + 1 < p := by have := i.isLt; omega
    rw [mul_smul, hC₁, cartier_pow_smul_D_eq_zero p C hC₁ hC₂ t hlt, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Unique

private theorem unique_of_pDigits [IsCurveOver K F] {t : F} (hdt : D K F t ≠ 0)
    (hdig : ∀ g : F, ∃ a : Fin p → F, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ))
    (C C' : Ω[F⁄K] →+ Ω[F⁄K])
    (hC₁ : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hC₂ : ∀ f : F, C (D K F f) = 0)
    (hC₃ : ∀ f : F, C (f ^ (p - 1) • D K F f) = D K F f)
    (hC'₁ : ∀ (f : F) (ω : Ω[F⁄K]), C' (f ^ p • ω) = f • C' ω)
    (hC'₂ : ∀ f : F, C' (D K F f) = 0)
    (hC'₃ : ∀ f : F, C' (f ^ (p - 1) • D K F f) = D K F f) : C = C' := by
  have hspan : Submodule.span F ({D K F t} : Set Ω[F⁄K]) = ⊤ :=
    kw_cart_hspan_of_isCurveOver hdt
  ext ω
  have hω : ω ∈ Submodule.span F ({D K F t} : Set Ω[F⁄K]) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨g, rfl⟩ := Submodule.mem_span_singleton.1 hω
  obtain ⟨a, rfl⟩ := hdig g
  rw [cartier_digits p C hC₁ hC₂ hC₃ t a, cartier_digits p C' hC'₁ hC'₂ hC'₃ t a]

end AlgebraicCurve.CartierOperatorConstruction

open AlgebraicCurve.CartierOperatorConstruction in
theorem _root_.AlgebraicCurve.cartierOperator_existsUnique {K : Type u} {F : Type v} [Field K]
  [Field F]
    [Algebra K F] [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP K p]
    [PerfectField K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    ∃! C : Ω[F⁄K] →+ Ω[F⁄K],
      (∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω) ∧
      (∀ f : F, C (KaehlerDifferential.D K F f) = 0) ∧
      (∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f) := by
  have : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  obtain ⟨t, hdt⟩ := AlgebraicCurve.exists_D_ne_zero (K := K) (F := F)
  have hdig : ∀ g : F, ∃ a : Fin p → F, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ) :=
    fun g => (AlgebraicCurve.pDigits_existsUnique p x hdt g).exists
  obtain ⟨C, hC₁, hC₂, hC₃⟩ := exists_cartierOperator p hdt hdig
  refine ⟨C, ⟨hC₁, hC₂, hC₃⟩, ?_⟩
  rintro C' ⟨hC'₁, hC'₂, hC'₃⟩
  exact (unique_of_pDigits p hdt hdig C C' hC₁ hC₂ hC₃ hC'₁ hC'₂ hC'₃).symm
end AlgebraicCurves.Differentials.Proofs.CartierOperator_existsUnique
end ProofImplementation

attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.KwCfx.kw_cfx_tau_coe
  AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff
  AlgebraicCurve.kw_hwcd_dlog_one
