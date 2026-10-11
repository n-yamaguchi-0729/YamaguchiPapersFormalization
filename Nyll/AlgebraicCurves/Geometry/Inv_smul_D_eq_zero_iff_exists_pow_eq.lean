/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_inv_smul_D_eq_zero_iff_exists_pow_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Differentials.Basic
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_exists_separating_transcendental
import Nyll.AlgebraicCurves.Differentials.Kaehler.KaehlerDifferential_D_ne_zero_of_transcendental
import Nyll.AlgebraicCurves.Differentials.Dvd_ord_of_isRegularDiff_dlog
import Nyll.AlgebraicCurves.Places.Place_D_ne_zero_of_ord_eq_one
import Nyll.AlgebraicCurves.Divisors.Divisor_exists_eq_pow_and_eq_ord_of_inv_smul_D_eq_zero
import Nyll.AlgebraicCurves.Differentials.Regular
import Nyll.AlgebraicCurves.Cohomology.LogDeRham

/-!
# Inv smul D eq zero iff exists pow eq
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Proofs.Inv_smul_D_eq_zero_iff_exists_pow_eq
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

open AlgebraicCurve

theorem _root_.AlgebraicCurve.inv_smul_D_eq_zero_iff_exists_pow_eq
    {K : Type*} [Field K] [PerfectField K] {F : Type*} [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (f : F) (hf : f ≠ 0) :
    f⁻¹ • KaehlerDifferential.D K F f = 0 ↔ ∃ g : F, g ^ p = f := by
  have : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  constructor
  · intro h0
    obtain ⟨t, ht, hfd, hsep⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
    have := hfd
    have := hsep
    have : FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := hfd
    have hdt : KaehlerDifferential.D K F t ≠ 0 := KaehlerDifferential.D_ne_zero_of_transcendental K
      t ht
    have hreg : IsRegularDiff K F (f⁻¹ • KaehlerDifferential.D K F f) := by
      rw [h0]
      intro v
      have hex : ∃ s : F, v.ord s = 1 := by
        obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
        exact ⟨(π : F), v.ord_coe_irreducible hπ⟩
      have hπ1 : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt hex
      have hDπ : KaehlerDifferential.D K F v.uniformizer_alt ≠ 0 := Place.D_ne_zero_of_ord_eq_one t
        v hπ1
      have hcoeff : Place.diffCoeff v.uniformizer_alt (0 : Ω[F⁄K]) = 0 := by
        have hexg : ∃ g : F, (0 : Ω[F⁄K]) = g • KaehlerDifferential.D K F v.uniformizer_alt := ⟨0,
          by rw [zero_smul]⟩
        have h := Place.diffCoeff_smul_D hexg
        exact (smul_eq_zero.mp h).resolve_right hDπ
      change 0 ≤ v.ordDiff 0
      rw [Place.ordDiff_def, hcoeff, Place.ord_zero]
    have hdvd : ∀ v : Place K F, (p : ℤ) ∣ v.ord f := AlgebraicCurve.dvd_ord_of_isRegularDiff_dlog
      p t hreg
    obtain ⟨D₀, hD₀, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf
    let D : Divisor K F := D₀.mapRange (fun n => n / (p : ℤ)) (by simp)
    have hD : ∀ v : Place K F, (p : ℤ) * D v = v.ord f := by
      intro v
      change (p : ℤ) * (D₀.mapRange (fun n => n / (p : ℤ)) (by simp) v) = v.ord f
      rw [Finsupp.mapRange_apply, hD₀ v]
      exact Int.mul_ediv_cancel' (hdvd v)
    obtain ⟨g, -, hfg, -⟩ :=
      AlgebraicCurve.Divisor.exists_eq_pow_and_eq_ord_of_inv_smul_D_eq_zero K F p t hsep hdt D f hf
        hD h0
    exact ⟨g, hfg.symm⟩
  · rintro ⟨g, rfl⟩
    have : KaehlerDifferential.D K F (g ^ p) = 0 := by
      rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F p, zero_smul]
    rw [this, smul_zero]
end AlgebraicCurves.Geometry.Proofs.Inv_smul_D_eq_zero_iff_exists_pow_eq
end ProofImplementation
