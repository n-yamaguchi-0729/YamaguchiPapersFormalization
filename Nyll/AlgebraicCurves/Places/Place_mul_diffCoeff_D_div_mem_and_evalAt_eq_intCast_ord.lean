/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_mul_diffCoeff_D_div_mem_and_evalAt_eq_intCast_ord.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.Basic
import Nyll.AlgebraicCurves.Places.Evaluation
import Nyll.AlgebraicCurves.Places.Place_diffCoeff_smul_D_of_ord_eq_one
import Nyll.AlgebraicCurves.Places.Place_diffCoeff_smul_D_eq_of_ord_eq_one
import Nyll.AlgebraicCurves.Places.Place_ord_diffCoeff_D_nonneg_of_perfectField
import Nyll.AlgebraicCurves.Places.Place_mem_iff_ord_nonneg

/-!
# Place mul diff Coeff D div mem and eval At eq int Cast ord
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_mul_diffCoeff_D_div_mem_and_evalAt_eq_intCast_ord

open _root_.AlgebraicCurve
open _root_.KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

section LogDeriv

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mul_derivation_mul_div_mul (δ : Derivation K F F) (t : F) {f g : F} (hf : f ≠ 0) (hg : g ≠
  0) :
    t * δ (f * g) / (f * g) = t * δ f / f + t * δ g / g := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

theorem mul_derivation_inv_div_inv (δ : Derivation K F F) (t : F) {f : F} (hf : f ≠ 0) :
    t * δ f⁻¹ / f⁻¹ = -(t * δ f / f) := by
  have h := mul_derivation_mul_div_mul δ t hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, Derivation.map_one_eq_zero, mul_zero, zero_div] at h
  linear_combination -h

theorem mul_derivation_zpow_div_zpow (δ : Derivation K F F) (t : F) {a : F} (ha : a ≠ 0) (n : ℤ) :
    t * δ (a ^ n) / a ^ n = (n : F) * (t * δ a / a) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one₀ ha, mul_derivation_mul_div_mul δ t (zpow_ne_zero _ ha) ha, ih]
    push_cast
    ring
  | pred n ih =>
    rw [zpow_sub_one₀ ha, mul_derivation_mul_div_mul δ t (zpow_ne_zero _ ha) (inv_ne_zero ha),
      mul_derivation_inv_div_inv δ t ha, ih]
    push_cast
    ring

end LogDeriv

section DerivOfUniformizer

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]

theorem diffCoeff_eq_of_eq_smul_D_of_ord_eq_one (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) {ω : Ω[F⁄K]} {g : F}
    (h : ω = g • KaehlerDifferential.D K F t) :
    diffCoeff t ω = g := by
  rw [h]
  exact diffCoeff_smul_D_eq_of_ord_eq_one x v ht g

/-- The derivation obtained by taking the differential coefficient with respect to a
uniformizer. -/
noncomputable def derivationOfOrdEqOne (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) : Derivation K F F where
  toFun f := diffCoeff t (KaehlerDifferential.D K F f)
  map_add' f g := by
    refine diffCoeff_eq_of_eq_smul_D_of_ord_eq_one x v ht ?_
    rw [map_add, add_smul, diffCoeff_smul_D_of_ord_eq_one x v ht,
      diffCoeff_smul_D_of_ord_eq_one x v ht]
  map_smul' a f := by
    refine diffCoeff_eq_of_eq_smul_D_of_ord_eq_one x v ht ?_
    rw [Derivation.map_smul, RingHom.id_apply, smul_assoc, diffCoeff_smul_D_of_ord_eq_one x v ht]
  map_one_eq_zero' := by
    change diffCoeff t (KaehlerDifferential.D K F 1) = 0
    refine diffCoeff_eq_of_eq_smul_D_of_ord_eq_one x v ht ?_
    rw [Derivation.map_one_eq_zero, zero_smul]
  leibniz' f g := by
    change diffCoeff t (KaehlerDifferential.D K F (f * g)) =
      f • diffCoeff t (KaehlerDifferential.D K F g) + g • diffCoeff t (KaehlerDifferential.D K F f)
    refine diffCoeff_eq_of_eq_smul_D_of_ord_eq_one x v ht ?_
    rw [Derivation.leibniz, add_smul, smul_eq_mul, smul_eq_mul, mul_smul, mul_smul,
      diffCoeff_smul_D_of_ord_eq_one x v ht, diffCoeff_smul_D_of_ord_eq_one x v ht]

theorem derivationOfOrdEqOne_apply (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) (f : F) :
    derivationOfOrdEqOne x v ht f = diffCoeff t (KaehlerDifferential.D K F f) := rfl

theorem derivationOfOrdEqOne_self (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) :
    derivationOfOrdEqOne x v ht t = 1 :=
  diffCoeff_eq_of_eq_smul_D_of_ord_eq_one x v ht (one_smul F _).symm

theorem derivationOfOrdEqOne_mem (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) {f : F} (hf : f ∈ v.toValuationSubring) :
    derivationOfOrdEqOne x v ht f ∈ v.toValuationSubring := by
  by_cases hf0 : f = 0
  · rw [hf0, map_zero]; exact zero_mem _
  by_cases hd : derivationOfOrdEqOne x v ht f = 0
  · rw [hd]; exact zero_mem _
  rw [mem_iff_ord_nonneg v hd, derivationOfOrdEqOne_apply]
  exact ord_diffCoeff_D_nonneg_of_perfectField x v ht ((mem_iff_ord_nonneg v hf0).mp hf)

end DerivOfUniformizer

end AlgebraicCurve.Place

open Place_mul_diffCoeff_D_div_mem_and_evalAt_eq_intCast_ord.AlgebraicCurve.Place in
theorem _root_.AlgebraicCurve.Place.mul_diffCoeff_D_div_mem_and_evalAt_eq_intCast_ord
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) {f : F} (hf : f ≠ 0) :
    t * Place.diffCoeff t (KaehlerDifferential.D K F f) / f ∈ v.toValuationSubring ∧
      v.evalAt (t * Place.diffCoeff t (KaehlerDifferential.D K F f) / f) = ((v.ord f : ℤ) : K) := by
  obtain ⟨δ, hδ, hδt, hδmem⟩ : ∃ δ : Derivation K F F,
      (∀ g : F, δ g = Place.diffCoeff t (KaehlerDifferential.D K F g)) ∧ δ t = 1 ∧
        ∀ g : F, g ∈ v.toValuationSubring → δ g ∈ v.toValuationSubring :=
    ⟨AlgebraicCurve.Place.derivationOfOrdEqOne x v ht, fun _ => rfl,
      AlgebraicCurve.Place.derivationOfOrdEqOne_self x v ht,
      fun _ hg => AlgebraicCurve.Place.derivationOfOrdEqOne_mem x v ht hg⟩
  rw [← hδ f]
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  have htmem : t ∈ v.toValuationSubring := (Place.mem_iff_ord_nonneg v ht0).mpr (by omega)
  set m : ℤ := v.ord f with hm
  have hw0 : f * t ^ (-m) ≠ 0 := mul_ne_zero hf (zpow_ne_zero _ ht0)
  have hordw : v.ord (f * t ^ (-m)) = 0 := by
    rw [Place.ord_mul _ hf (zpow_ne_zero _ ht0), Place.ord_zpow, ht]; ring
  have hwmem : f * t ^ (-m) ∈ v.toValuationSubring :=
    (Place.mem_iff_ord_nonneg v hw0).mpr hordw.ge
  have hwinv : (f * t ^ (-m))⁻¹ ∈ v.toValuationSubring :=
    (Place.mem_iff_ord_nonneg v (inv_ne_zero hw0)).mpr (by rw [Place.ord_inv, hordw, neg_zero])
  have hδw : δ (f * t ^ (-m)) ∈ v.toValuationSubring := hδmem _ hwmem
  have hf_eq : f = (f * t ^ (-m)) * t ^ m := by
    rw [mul_assoc, ← zpow_add₀ ht0, neg_add_cancel, zpow_zero, mul_one]
  have halg : algebraMap K F (m : K) ∈ v.toValuationSubring := by
    rw [← Place.coe_algebraMap]; exact SetLike.coe_mem _
  have key : t * δ f / f = t * (δ (f * t ^ (-m)) * (f * t ^ (-m))⁻¹) + algebraMap K F (m : K) := by
    conv_lhs => rw [hf_eq]
    rw [mul_derivation_mul_div_mul δ t hw0 (zpow_ne_zero m ht0),
      mul_derivation_zpow_div_zpow δ t ht0 m, hδt, map_intCast]
    field_simp
  have hmem : t * (δ (f * t ^ (-m)) * (f * t ^ (-m))⁻¹) + algebraMap K F (m : K) ∈
    v.toValuationSubring :=
    add_mem (mul_mem htmem (mul_mem hδw hwinv)) halg
  rw [key]
  refine ⟨hmem, ?_⟩
  rw [Place.evalAt_of_mem v hmem]
  have htunit : ¬ IsUnit (⟨t, htmem⟩ : v.toValuationSubring) := by
    intro hu
    have := v.ord_coe_unit hu.unit
    simp only [IsUnit.unit_spec] at this
    rw [ht] at this
    exact one_ne_zero this
  have hres_t : IsLocalRing.residue v.toValuationSubring ⟨t, htmem⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr htunit)
  have helt : (⟨_, hmem⟩ : v.toValuationSubring) =
      ⟨t, htmem⟩ * (⟨_, hδw⟩ * ⟨_, hwinv⟩) + algebraMap K v.toValuationSubring (m : K) :=
    Subtype.ext rfl
  rw [helt, map_add, map_mul, hres_t, zero_mul, zero_add]
  have hsc : IsLocalRing.residue v.toValuationSubring (algebraMap K v.toValuationSubring (m : K)) =
      algebraMap K v.ResidueField (m : K) := rfl
  rw [hsc, Place.residueInv_algebraMap]
end AlgebraicCurves.Places.Proofs.Place_mul_diffCoeff_D_div_mem_and_evalAt_eq_intCast_ord
end ProofImplementation
