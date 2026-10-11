/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_hasPoleOrderLE_one_inv_smul_D_and_hasLogResidue_intCast_ord.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Differentials.Regular
import Nyll.AlgebraicCurves.Cohomology.LogDeRham
import Nyll.AlgebraicCurves.Differentials.Basic
import Nyll.AlgebraicCurves.Places.Evaluation
import Nyll.AlgebraicCurves.Places.Place_exists_irreducible_dCoord_eq_D_and_hasPoleOrderLE_iff
import Nyll.AlgebraicCurves.Places.Place_mul_diffCoeff_D_div_mem_and_evalAt_eq_intCast_ord
import Nyll.AlgebraicCurves.Places.Place_D_ne_zero_of_ord_eq_one
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_exists_separating_transcendental

/-!
# Place has Pole Order LE one inv smul D and has Log Residue int Cast ord
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_hasPoleOrderLE_one_inv_smul_D_and_hasLogResidue_intCast_ord
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

theorem _root_.AlgebraicCurve.Place.hasPoleOrderLE_one_inv_smul_D_and_hasLogResidue_intCast_ord
    {K : Type*} [Field K] [IsAlgClosed K] {F : Type*} [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (f : F) (hf : f ≠ 0) (v : Place K F) :
    v.HasPoleOrderLE 1 (f⁻¹ • KaehlerDifferential.D K F f) ∧
      v.HasLogResidue (f⁻¹ • KaehlerDifferential.D K F f) ((v.ord f : ℤ) : K) := by
  obtain ⟨π, hπirr, hπd, hpole, -, hres⟩ :=
    Place.exists_irreducible_dCoord_eq_D_and_hasPoleOrderLE_iff v
  set t : F := (π : F) with ht_def
  have ht : v.ord t = 1 := v.ord_coe_irreducible hπirr
  obtain ⟨x, hx, hfd, hsep⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F := hfd
  have hDt : KaehlerDifferential.D K F t ≠ 0 := Place.D_ne_zero_of_ord_eq_one x v ht
  have h1 : Module.finrank F (Ω[F⁄K]) = 1 := (IsCurveOver.kaehler_free_rank_one (K := K) (F := F)).2
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (KaehlerDifferential.D K F t) hDt).mp h1
    (KaehlerDifferential.D K F f)
  set g : F := Place.diffCoeff t (KaehlerDifferential.D K F f) with hg_def
  have hg : g • KaehlerDifferential.D K F t = KaehlerDifferential.D K F f := Place.diffCoeff_smul_D
    ⟨c, hc.symm⟩
  obtain ⟨hmem, heval⟩ := Place.mul_diffCoeff_D_div_mem_and_evalAt_eq_intCast_ord (K := K) x v ht hf
  have hdlog : f⁻¹ • KaehlerDifferential.D K F f = (g / f) • v.dCoord := by
    rw [hπd, ← hg, smul_smul, div_eq_inv_mul]
  have hkey : t * (g / f) = t * Place.diffCoeff t (KaehlerDifferential.D K F f) / f := by
    rw [hg_def, mul_div_assoc]
  refine ⟨(hpole 1 _).mpr ⟨g / f, ?_, hdlog⟩, (hres _ _).mpr ⟨g / f, hdlog, ?_⟩⟩
  · rw [pow_one, hkey]; exact hmem
  · have hrat : v.IsRational := by
      have : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
      have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
      exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2
    rw [hkey]
    exact ⟨hmem, by rw [← v.algebraMap_evalAt hrat hmem, heval]⟩
end AlgebraicCurves.Places.Proofs.Place_hasPoleOrderLE_one_inv_smul_D_and_hasLogResidue_intCast_ord
end ProofImplementation

attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
