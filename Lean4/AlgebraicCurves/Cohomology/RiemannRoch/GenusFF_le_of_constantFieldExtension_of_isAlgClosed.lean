/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_genusFF_le_of_constantFieldExtension_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Places.Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
import AlgebraicCurves.Cohomology.RiemannRoch.Ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed
import AlgebraicCurves.Cohomology.RiemannRoch.Exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed
import AlgebraicCurves.Cohomology.RiemannRoch.Exists_genus_riemannIndex_of_isCurveOver
import AlgebraicCurves.Cohomology.RiemannRoch.StichtenothGenusExists_of_isCurveOver
import AlgebraicCurves.Cohomology.IndexOfSpecialty_eq_finrank_H1
import AlgebraicCurves.FunctionFields.EssFiniteType_of_transcendental_of_finiteDimensional
import AlgebraicCurves.Places.Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import AlgebraicCurves.Divisors.Divisor_degree_eq_sum_support
import AlgebraicCurves.Cohomology.RiemannRoch.FiniteDimensional_lSpace

/-!
# Genus FF le of constant Field Extension of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.GenusFFLeConstantsAlgClosed
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open AlgebraicCurve

namespace W7XGenusFFLE

theorem constantsAreBase {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ConstantsAreBase K F := by
  obtain ⟨x, hxt, hxfd⟩ := hfg
  have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  refine le_antisymm (fun f hf => ?_) (fun f ⟨c, hc⟩ => hc ▸ fun v =>
    Place.adicValuation_algebraMap_le_one v c)
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  have hord : ∀ v : Place K F, 0 ≤ v.ord f := fun v => by
    have := (mem_riemannRochSpace_iff.mp hf v).resolve_left hf0; simpa using this
  obtain ⟨Df, hDord, hDdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf0
  have hdiv : ∀ v : Place K F, v.ord f = 0 := by
    by_contra hne; push Not at hne; obtain ⟨v, hv⟩ := hne
    refine absurd hDdeg (ne_of_gt ?_)
    rw [Divisor.degree_eq_sum_support]
    refine Finset.sum_pos' (fun w _ => mul_nonneg (by rw [hDord w]; exact hord w)
      (Int.natCast_nonneg _)) ⟨v, ?_, ?_⟩
    · simp only [Finsupp.mem_support_iff, hDord v]; exact hv
    · rw [hDord v]
      have : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
      have : (v.deg : ℤ) = 1 := by exact_mod_cast Place.deg_eq_one_of_isAlgClosed_of_finite v
      rw [this, mul_one]; exact (hord v).lt_of_ne' hv
  exact ⟨_, (Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed x hxt
    (F := F) hdiv).choose_spec⟩

end W7XGenusFFLE

open W7XGenusFFLE

theorem _root_.AlgebraicCurve.genusFF_le_of_constantFieldExtension_of_isAlgClosed (K F K' F' :
  Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤) :
    genusFF K' F' ≤ genusFF K F := by
  classical
  obtain ⟨x, hxt, hxfd⟩ := id hfg
  obtain ⟨x', hxt', hxfd'⟩ := id hfg'
  have : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional hxt hxfd
  have : Algebra.EssFiniteType K' F' :=
    essFiniteType_of_transcendental_of_finiteDimensional hxt' hxfd'
  have hCAB : ConstantsAreBase K F := constantsAreBase hfg
  have hCAB' : ConstantsAreBase K' F' := constantsAreBase hfg'
  have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  have : HasPrincipalDivisors K' F' := IsCurveOver.hasPrincipalDivisors
  obtain ⟨γ, hγ⟩ := exists_genus_riemannIndex_of_isCurveOver (K := K) (F := F) hCAB
  obtain ⟨γ', hγ'⟩ := exists_genus_riemannIndex_of_isCurveOver (K := K') (F := F') hCAB'
  have hγeq : γ = (genusFF K F : ℤ) := by
    have h0 := (hγ 0).2
    rw [show Divisor.degree (0 : Divisor K F) = 0 from map_zero _,
      ell_zero_eq_one_of_constantsAreBase hCAB,
      indexOfSpecialty_eq_finrank_H1 (K := K) (F := F) 0] at h0
    unfold genusFF; push_cast at h0 ⊢; linarith
  have hγeq' : γ' = (genusFF K' F' : ℤ) := by
    have h0 := (hγ' 0).2
    rw [show Divisor.degree (0 : Divisor K' F') = 0 from map_zero _,
      ell_zero_eq_one_of_constantsAreBase hCAB',
      indexOfSpecialty_eq_finrank_H1 (K := K') (F := F') 0] at h0
    unfold genusFF; push_cast at h0 ⊢; linarith
  have hX := fun P =>
    Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
      K F K' F' hfg hfg' hgen P
  choose lift hlift_comap hlift_ord hlift_uniq using hX
  have hlift_inj : Function.Injective lift := fun P Q h => by
    have hP := hlift_comap P; have hQ := h ▸ hlift_comap Q
    exact Place.ext (hP.symm.trans hQ)
  have hlift_new : ∀ v' : Place K' F', (∀ v, lift v ≠ v') →
      ∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring :=
    fun v' hnv v hcomap => hnv v ((hlift_uniq v v' hcomap).symm)
  have : ∀ v : Place K F, Module.Finite K v.ResidueField := fun v => IsCurveOver.finiteResidue v
  have : ∀ v' : Place K' F', Module.Finite K' v'.ResidueField :=
    fun v' => IsCurveOver.finiteResidue v'
  obtain ⟨D, hiD'⟩ :=
    exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed
      K F K' F' hfg hfg' hgen lift hlift_ord hlift_inj
  set D' : Divisor K' F' := Finsupp.mapDomain lift D with hD'def
  have hdegEq : Divisor.degree D' = Divisor.degree D := by
    rw [Divisor.degree_eq_sum_support, Divisor.degree_eq_sum_support, hD'def,
      Finsupp.mapDomain_support_of_injective hlift_inj,
      Finset.sum_image (fun a _ b _ h => hlift_inj h)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finsupp.mapDomain_apply_of_injective hlift_inj,
      show ((lift v).deg : ℤ) = 1 from by
        exact_mod_cast Place.deg_eq_one_of_isAlgClosed_of_finite (lift v),
      show ((v.deg : ℤ)) = 1 from by exact_mod_cast Place.deg_eq_one_of_isAlgClosed_of_finite v]
  obtain ⟨hne, hfd0, γ₀, D₀, hD₀⟩ := stichtenothGenusExists_of_isCurveOver (K := K) (F := F) hCAB
  have : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := hfd0
  have hfdD : FiniteDimensional K ↥(riemannRochSpace D) := finiteDimensional_lSpace D
  have hellEq : ell (K := K') D' = ell (K := K) D := by
    rw [hD'def]
    exact ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed K F K' F' hfg hfg' hgen
      lift hlift_ord hlift_inj hlift_new D
  have hiD : (0:ℤ) ≤ γ - γ' := by
    have h1 := (hγ' D').2
    rw [hiD', Nat.cast_zero] at h1
    have h2 : (ell (K := K') D' : ℤ) = Divisor.degree D' + 1 - γ' := by linarith
    rw [hdegEq, hellEq] at h2
    have h3 := (hγ D).2
    have hnn : (0:ℤ) ≤ (indexOfSpecialty (K := K) D : ℤ) := Int.natCast_nonneg _
    linarith
  have hγle : γ' ≤ γ := by linarith
  rw [hγeq, hγeq'] at hγle
  exact_mod_cast hγle
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.GenusFFLeConstantsAlgClosed
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
