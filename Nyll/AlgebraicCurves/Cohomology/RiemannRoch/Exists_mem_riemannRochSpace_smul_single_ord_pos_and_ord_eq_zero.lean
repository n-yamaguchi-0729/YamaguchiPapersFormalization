/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_exists_separating_transcendental
import Nyll.AlgebraicCurves.Places.Place_deg_eq_one_of_isAlgClosed
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.FiniteDimensional_lSpace
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.FiniteDimensional_lSpace_zero

/-!
# Exists mem riemann Roch Space smul single ord pos and ord eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsMemRRSpaceSmulSingleOrdPos
open _root_.AlgebraicCurve.Place in
open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  AlgebraicCurve.Pic0.instModuleZModTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instSMulTorsion
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
  kw_ffgc_finiteDimensional_adicCompletion
  kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  kw_ffgc_continuousSMul_adicCompletionComap
  kw_ffgc_isScalarTower_integersCompletionCompletion
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
attribute [-instance] AlgebraicCurve.instHasCanonicalLocalResidueK
  AlgebraicCurve.Place.instAlgebra_restrictResidueField
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv
  AlgebraicCurve.SemilinearAut.smul_def
attribute [-simp] AlgebraicCurve.SemilinearAut.smul_single
  AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv
  AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul
  AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom
  AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

open AlgebraicCurve

namespace SepR

variable {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F]
  [Algebra.EssFiniteType k F]

omit [Algebra.EssFiniteType k F] in
theorem deg_eq_one (v : Place k F) : v.deg = 1 := by
  apply AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed
  have : Module.Finite k v.ResidueField := IsCurveOver.finiteResidue v
  exact (Module.finrank_pos (R := k) (M := v.ResidueField)).ne'

theorem finrank_riemannRochSpace_eq (D : Divisor k F) (hD : 2 * (genusFF k F : ℤ) - 1 ≤ D.degree) :
    (Module.finrank k ↥(riemannRochSpace D) : ℤ) = D.degree + 1 - (genusFF k F : ℤ) := by
  obtain ⟨t, ht, hfin, hsep⟩ := AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K :=
    k) (F := F)
  exact AlgebraicCurve.ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable k t ht hfin
    hsep D hD
omit [IsAlgClosed k] in
theorem finiteDimensional_riemannRochSpace (P : Place k F) (D : Divisor k F) :
    FiniteDimensional k ↥(riemannRochSpace D) := by
  have : Nonempty (Place k F) := ⟨P⟩
  have : FiniteDimensional k ↥(LSpace (0 : Divisor k F)) :=
    AlgebraicCurve.finiteDimensional_lSpace_zero k F
  exact AlgebraicCurve.finiteDimensional_lSpace D
omit [IsAlgClosed k] [IsCurveOver k F] [Algebra.EssFiniteType k F] in
theorem riemannRochSpace_mono {D D' : Divisor k F} (h : ∀ v, D v ≤ D' v) : riemannRochSpace D ≤
  riemannRochSpace D' := by
  intro f hf
  rw [mem_riemannRochSpace_iff] at hf ⊢
  intro v
  rcases hf v with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (le_trans (neg_le_neg (h v)) h1)

end SepR

open SepR

theorem _root_.AlgebraicCurve.exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero
    (k F : Type*) [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F]
      [Algebra.EssFiniteType k F]
    (c s s' : Place k F) (hsc : s ≠ c) (hs'c : s' ≠ c) (hss' : s ≠ s') :
    ∃ g : F, g ∈ riemannRochSpace (((2 * genusFF k F + 1 : ℕ) : ℤ) • Finsupp.single c (1 : ℤ)) ∧
      0 < s.ord g ∧ s'.ord g = 0 := by
  classical
  set G := genusFF k F with hG
  set E : Divisor k F := (((2 * genusFF k F + 1 : ℕ) : ℤ) • Finsupp.single c (1 : ℤ)) with hE
  set E₁ : Divisor k F := E - Finsupp.single s (1 : ℤ) with hE₁
  set E₂ : Divisor k F := E₁ - Finsupp.single s' (1 : ℤ) with hE₂
  have hEv : ∀ v, E v = if c = v then (2 * (G : ℤ) + 1) else 0 := by
    intro v
    rw [hE, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> push_cast <;> ring
  have hE₁v : ∀ v, E₁ v = E v - if s = v then 1 else 0 := by
    intro v; rw [hE₁, Finsupp.sub_apply, Finsupp.single_apply]
  have hE₂v : ∀ v, E₂ v = E₁ v - if s' = v then 1 else 0 := by
    intro v; rw [hE₂, Finsupp.sub_apply, Finsupp.single_apply]
  have hdegE : E.degree = 2 * (G : ℤ) + 1 := by
    rw [hE, map_zsmul, Divisor.degree_single, deg_eq_one (k := k) c]; push_cast; ring
  have hdegE₁ : E₁.degree = 2 * (G : ℤ) := by
    rw [hE₁, map_sub, hdegE, Divisor.degree_single, deg_eq_one (k := k) s]; push_cast; ring
  have hdegE₂ : E₂.degree = 2 * (G : ℤ) - 1 := by
    rw [hE₂, map_sub, hdegE₁, Divisor.degree_single, deg_eq_one (k := k) s']; push_cast; ring
  have h₁ := finrank_riemannRochSpace_eq (k := k) E₁ (by rw [hdegE₁]; omega)
  have h₂ := finrank_riemannRochSpace_eq (k := k) E₂ (by rw [hdegE₂])
  rw [hdegE₁] at h₁
  rw [hdegE₂] at h₂
  have := finiteDimensional_riemannRochSpace (k := k) c E₁
  have hle : riemannRochSpace E₂ ≤ riemannRochSpace E₁ :=
    riemannRochSpace_mono fun v => by rw [hE₂v]; split_ifs <;> omega
  have hlt : riemannRochSpace E₂ < riemannRochSpace E₁ := by
    apply Submodule.lt_of_le_of_finrank_lt_finrank hle
    have : (Module.finrank k ↥(riemannRochSpace E₂) : ℤ) < Module.finrank k ↥(riemannRochSpace E₁)
      := by
      rw [h₁, h₂]; omega
    exact_mod_cast this
  obtain ⟨g, hg₁, hg₂⟩ := IsConcreteLE.exists_of_lt hlt
  have hg₁' := mem_riemannRochSpace_iff.mp hg₁
  have hg0 : g ≠ 0 := by
    rintro rfl; exact hg₂ (Submodule.zero_mem _)
  have hords : 0 < s.ord g := by
    rcases hg₁' s with h0 | h
    · exact absurd h0 hg0
    · rw [hE₁v, hEv, ite_eq_right (Ne.symm hsc), ite_eq_left rfl] at h
      omega
  have hords'0 : 0 ≤ s'.ord g := by
    rcases hg₁' s' with h0 | h
    · exact absurd h0 hg0
    · rw [hE₁v, hEv, ite_eq_right (Ne.symm hs'c), ite_eq_right hss'] at h
      omega
  have hords' : s'.ord g = 0 := by
    by_contra hne
    apply hg₂
    rw [mem_riemannRochSpace_iff]
    intro v
    right
    by_cases hv : s' = v
    · subst hv
      rw [hE₂v, hE₁v, hEv, ite_eq_right (Ne.symm hs'c), ite_eq_right hss', ite_eq_left rfl]
      omega
    · rw [hE₂v, ite_eq_right hv, sub_zero]
      rcases hg₁' v with h0 | h
      · exact absurd h0 hg0
      · exact h
  refine ⟨g, ?_, hords, hords'⟩
  exact riemannRochSpace_mono (fun v => by rw [hE₁v]; split_ifs <;> omega) hg₁
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsMemRRSpaceSmulSingleOrdPos
end ProofImplementation

attribute [-simp] AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Place.congrEquiv_symm_apply
attribute [-simp] AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv
  AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single
  AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv
  AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul
  AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom
  AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul
attribute [-simp] AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
