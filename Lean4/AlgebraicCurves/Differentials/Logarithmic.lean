/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Differentials.Order

/-!
# Logarithmic
-/

open KaehlerDifferential

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

/-- Membership in a place's valuation ring, expressed by nonnegative order. -/
theorem kw_hwcd_mem_of_ord_nonneg {z : F} (h : 0 ≤ v.ord z) :
    z ∈ v.toValuationSubring := by
  rcases eq_or_ne z 0 with rfl | hz
  · exact zero_mem _
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hz hπ
    have hn : v.ord z = (((v.ord z).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg h).symm
    rw [hu, hn, zpow_natCast]
    exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 _)

/-- Elements of a place's valuation ring have nonnegative order. -/
theorem kw_hwcd_ord_nonneg_of_mem {z : F} (hz : z ∈ v.toValuationSubring) :
    0 ≤ v.ord z := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [v.ord_zero]
  by_contra hneg
  rw [Int.not_le] at hneg
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hz0 hπ
  have hπF : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  set m : ℕ := (-(v.ord z)).toNat with hm
  have hm_pos : 0 < m := by omega
  have hmz : (m : ℤ) = -(v.ord z) := Int.toNat_of_nonneg (by omega)
  have hkey : ((π : F) ^ m) * (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) * z
      = 1 := by
    rw [hu]
    have huu : (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F)
        * (((u : v.toValuationSubring)) : F) = 1 := by
      norm_cast
      simp
    calc ((π : F) ^ m) * (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F)
          * (((u : v.toValuationSubring) : F) * ((π : F) ^ (v.ord z)))
        = ((((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F)
            * ((u : v.toValuationSubring) : F)) * (((π : F) ^ m) * ((π : F) ^ (v.ord z))) := by
          ring
      _ = ((π : F) ^ (m : ℤ)) * ((π : F) ^ (v.ord z)) := by
          rw [huu, one_mul, zpow_natCast]
      _ = (π : F) ^ ((m : ℤ) + v.ord z) := (zpow_add₀ hπF _ _).symm
      _ = 1 := by rw [hmz]; simp
  have hmem : ((π : v.toValuationSubring) ^ m)
      * ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) * ⟨z, hz⟩ = 1 := by
    apply Subtype.ext
    push_cast
    exact hkey
  have hunit : IsUnit ((π : v.toValuationSubring) ^ m) :=
    IsUnit.of_mul_eq_one _ (by rw [mul_assoc] at hmem; exact hmem)
  exact hπ.not_isUnit ((isUnit_pow_iff hm_pos.ne').mp hunit)

/-- A nonzero constant has order zero at every place. -/
theorem kw_hwcd_ord_algebraMap {a : K} (ha : a ≠ 0) :
    v.ord (algebraMap K F a) = 0 := by
  have hmem : algebraMap K F a ∈ v.toValuationSubring := v.algebraMap_mem' a
  have hmem' : algebraMap K F a⁻¹ ∈ v.toValuationSubring := v.algebraMap_mem' a⁻¹
  have hprod : (⟨_, hmem⟩ * ⟨_, hmem'⟩ : v.toValuationSubring) = 1 := by
    apply Subtype.ext
    change (algebraMap K F a) * (algebraMap K F a⁻¹) = 1
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  have hunit : IsUnit (⟨algebraMap K F a, hmem⟩ : v.toValuationSubring) :=
    IsUnit.of_mul_eq_one _ hprod
  simpa using v.ord_coe_unit hunit.unit

end Place

/-- The logarithmic differential `df / f`. -/
def kw_hwcd_dlog (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (f : F) :
    Ω[F⁄K] :=
  f⁻¹ • KaehlerDifferential.D K F f
@[simp]
theorem kw_hwcd_dlog_zero : kw_hwcd_dlog K (0 : F) = 0 := by
  rw [kw_hwcd_dlog, map_zero, smul_zero]
@[simp]
theorem kw_hwcd_dlog_one : kw_hwcd_dlog K (1 : F) = 0 := by
  rw [kw_hwcd_dlog, Derivation.map_one_eq_zero, smul_zero]

theorem kw_hwcd_dlog_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    kw_hwcd_dlog K (f * g) = kw_hwcd_dlog K f + kw_hwcd_dlog K g := by
  rw [kw_hwcd_dlog, kw_hwcd_dlog, kw_hwcd_dlog, Derivation.leibniz, smul_add,
    smul_smul, smul_smul, mul_inv]
  rw [show f⁻¹ * g⁻¹ * f = g⁻¹ by field_simp,
    show f⁻¹ * g⁻¹ * g = f⁻¹ by field_simp, add_comm]

theorem kw_hwcd_dlog_pow (n : ℕ) {f : F} (hf : f ≠ 0) :
    kw_hwcd_dlog K (f ^ n) = n • kw_hwcd_dlog K f := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, kw_hwcd_dlog_mul (pow_ne_zero k hf) hf, ih, succ_nsmul]

theorem kw_hwcd_dlog_pow_char (ℓ : ℕ) [CharP F ℓ] {f : F} (hf : f ≠ 0) :
    kw_hwcd_dlog K (f ^ ℓ) = 0 := by
  rw [kw_hwcd_dlog_pow ℓ hf, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F ℓ, zero_smul]

section Regular

variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem kw_hwcd_differentialCoeff_add (v : Place K F) (ω ω' : Ω[F⁄K]) :
    v.differentialCoeff (ω + ω')
      = v.differentialCoeff ω + v.differentialCoeff ω' :=
  v.differentialCoeff_unique
    (by rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

/-- Differentials regular at every place. -/
def kw_hwcd_regularDifferentials (K F : Type*) [Field K] [Field F] [Algebra K F]
    [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]] : Submodule K Ω[F⁄K] where
  carrier := {ω | ∀ v : Place K F, 0 ≤ v.ordDifferential ω}
  zero_mem' := by
    intro v
    rw [Place.ordDifferential, v.differentialCoeff_zero, v.ord_zero]
  add_mem' := by
    intro ω ω' hω hω' v
    rw [Place.ordDifferential, kw_hwcd_differentialCoeff_add]
    have h₁ : v.differentialCoeff ω ∈ v.toValuationSubring :=
      Place.kw_hwcd_mem_of_ord_nonneg v (hω v)
    have h₂ : v.differentialCoeff ω' ∈ v.toValuationSubring :=
      Place.kw_hwcd_mem_of_ord_nonneg v (hω' v)
    exact v.kw_hwcd_ord_nonneg_of_mem (add_mem h₁ h₂)
  smul_mem' := by
    intro a ω hω v
    rcases eq_or_ne a 0 with rfl | ha
    · rw [zero_smul, Place.ordDifferential, v.differentialCoeff_zero, v.ord_zero]
    have hsmul : a • ω = (algebraMap K F a) • ω := (algebraMap_smul F a ω).symm
    rw [Place.ordDifferential, hsmul, v.differentialCoeff_smul]
    rcases eq_or_ne (v.differentialCoeff ω) 0 with hc | hc
    · rw [hc, mul_zero, v.ord_zero]
    have hmap : algebraMap K F a ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K F).injective).mpr ha
    rw [v.ord_mul hmap hc, v.kw_hwcd_ord_algebraMap ha, zero_add]
    exact hω v
@[simp]
theorem kw_hwcd_mem_regularDifferentials_iff {ω : Ω[F⁄K]} :
    ω ∈ kw_hwcd_regularDifferentials K F
      ↔ ∀ v : Place K F, 0 ≤ v.ordDifferential ω :=
  Iff.rfl

end Regular

end AlgebraicCurve

end
