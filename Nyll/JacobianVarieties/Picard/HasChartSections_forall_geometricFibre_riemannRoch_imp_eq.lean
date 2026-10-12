/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_HasChartSections_forall_geometricFibre_riemannRoch_imp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.ChartSections
import Nyll.AlgebraicCurves.Models.CurveModel_eq_genusFF_of_forall_ell_sub_ell_eq
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.GenusFF_eq_of_algEquiv
import Nyll.AlgebraicCurves.Geometry.Nonempty_algEquiv_functionField_of_iso

/-!
Identify geometric-fibre invariants using chart sections and the function-field Riemann--Roch
comparison.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.HasChartSections_forall_geometricFibre_riemannRoch_imp_eq
attribute [-instance]
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance]
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp]
  AlgebraicCurve.Divisor.evalFun_zero
  AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec
  AlgebraicCurve.PoleDivisorPackage.mk.injEq
attribute [-simp]
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
    NeronModelInfra AlgebraicCurve

theorem _root_.AlgebraicGeometry.RelPicard.HasChartSections.forall_geometricFibre_riemannRoch_imp_eq
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {n g r : ℕ} {γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    (hγ : HasChartSections c γ) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g := by
  intro k _ _ s L _ _ M e he Kc g' hRR
  obtain ⟨L₀, iF, iA, M₀, e₀, he₀, ⟨Kc₀, hRR₀⟩, -⟩ := hγ k s
  have h1 : g' = genusFF k L := CurveModel.eq_genusFF_of_forall_ell_sub_ell_eq M hRR
  have h0 : g = genusFF k L₀ := CurveModel.eq_genusFF_of_forall_ell_sub_ell_eq M₀ hRR₀
  have hφ : (e ≪≫ e₀.symm).hom ≫ M₀.toBase = M.toBase := by
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← he₀, e₀.inv_hom_id_assoc, he]
  obtain ⟨ψ⟩ := AlgebraicCurve.nonempty_algEquiv_functionField_of_iso M.toBase M₀.toBase (e ≪≫
    e₀.symm) hφ
  let := M.functionFieldAlgebra
  let := M₀.functionFieldAlgebra
  have σ : L ≃ₐ[k] L₀ := (M.ffAlgEquiv.trans ψ).trans M₀.ffAlgEquiv.symm
  rw [h1, h0]
  exact genusFF_eq_of_algEquiv σ
end JacobianVarieties.Picard.Proofs.HasChartSections_forall_geometricFibre_riemannRoch_imp_eq
end ProofImplementation
