/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import AlgebraicCurves.Divisors.ClassGroup

/-!
# Place exists comap eq to Valuation Subring
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.PlaceExistsComapToValuation

open IsDedekindDomain

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

theorem rowMain (v : Place K F) :
    ∃ w : Place K F', w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring := by
  classical
  let A : Type _ := v.toValuationSubring
  let : Algebra A F' := ((algebraMap F F').comp (algebraMap A F)).toAlgebra
  have : IsScalarTower A F F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let C : Type _ := integralClosure A F'
  have : IsDedekindDomain C := integralClosure.isDedekindDomain A F F'
  have : IsFractionRing C F' := integralClosure.isFractionRing_of_finite_extension F F'
  let : Algebra K C := ((algebraMap A C).comp (algebraMap K A)).toAlgebra
  have hAC : ∀ a : A, algebraMap C F' (algebraMap A C a) = algebraMap F F' (a : F) := fun a => rfl
  have : IsScalarTower K C F' := IsScalarTower.of_algebraMap_eq (fun a => by
    change algebraMap K F' a = algebraMap C F' (algebraMap A C (algebraMap K A a))
    rw [hAC, Place.coe_algebraMap, ← IsScalarTower.algebraMap_apply])
  have hinj : Function.Injective (algebraMap A C) := by
    intro a b h
    have h' := congrArg (algebraMap C F') h
    rw [hAC, hAC] at h'
    exact Subtype.ext ((algebraMap F F').injective h')
  obtain ⟨P, hPmax, hP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := C)
    (IsLocalRing.maximalIdeal A) (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _))
  have hPne : P ≠ ⊥ := by
    intro hbot
    apply IsDiscreteValuationRing.not_a_field A
    rw [← hP, hbot]
    exact Ideal.comap_bot_of_injective _ hinj
  let w₀ : HeightOneSpectrum C := ⟨P, hPmax.isPrime, hPne⟩
  refine ⟨Place.ofHeightOneSpectrum (K := K) w₀, ?_⟩
  ext f
  rw [ValuationSubring.mem_comap, Place.ofHeightOneSpectrum_toValuationSubring,
    Valuation.mem_valuationSubring_iff]
  constructor
  · intro hle
    by_contra hfA
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact hfA (zero_mem _)
    have hinvA : f⁻¹ ∈ v.toValuationSubring :=
      (v.toValuationSubring.mem_or_inv_mem f).resolve_left hfA
    have hnu : (⟨f⁻¹, hinvA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
      have hb' : f⁻¹ * (b : F) = 1 := by simpa [Subtype.ext_iff] using hb
      have hbf : (b : F) = f := by
        have := congrArg (fun z => f * z) hb'
        simpa [← mul_assoc, mul_inv_cancel₀ hf0] using this
      exact hfA (hbf ▸ b.2)
    have hP' : algebraMap A C ⟨f⁻¹, hinvA⟩ ∈ P := by
      change (⟨f⁻¹, hinvA⟩ : A) ∈ P.under A
      rw [hP]
      exact hnu
    have hlt : w₀.valuation F' (algebraMap F F' f⁻¹) < 1 := by
      rw [show algebraMap F F' f⁻¹ = algebraMap C F' (algebraMap A C ⟨f⁻¹, hinvA⟩) from
        (hAC ⟨f⁻¹, hinvA⟩).symm]
      exact (w₀.valuation_lt_one_iff_mem _).mpr hP'
    rw [map_inv₀, map_inv₀] at hlt
    have hx0 : w₀.valuation F' (algebraMap F F' f) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr ((map_ne_zero _).mpr hf0)
    have : 1 < w₀.valuation F' (algebraMap F F' f) := (inv_lt_one₀ (zero_lt_iff.mpr hx0)).mp hlt
    exact absurd hle (not_le.mpr this)
  · intro hfA
    rw [show algebraMap F F' f = algebraMap C F' (algebraMap A C ⟨f, hfA⟩) from (hAC ⟨f, hfA⟩).symm]
    exact w₀.valuation_le_one _

end AlgebraicCurve.Place

open _root_.AlgebraicCurve
  _root_.AlgebraicCurves.Places.Proofs.PlaceExistsComapToValuation.AlgebraicCurve in
theorem _root_.AlgebraicCurve.Place.exists_comap_eq_toValuationSubring {K F F' : Type*} [Field K]
  [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F) :
    ∃ w : Place K F', w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring :=
  AlgebraicCurve.Place.rowMain v
end AlgebraicCurves.Places.Proofs.PlaceExistsComapToValuation
end ProofImplementation
