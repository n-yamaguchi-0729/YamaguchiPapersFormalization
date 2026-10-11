/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_int_forall_degree_add_one_sub_le_ell.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Differentials.Exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
import AlgebraicCurves.Cohomology.RiemannRoch.FiniteDimensional_lSpace_zero
import AlgebraicCurves.Places.Rational.RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower
import AlgebraicCurves.Cohomology.RiemannRoch.Exists_genus_riemannIndex_of_stichtenothGenusExists

/-!
# Exists int forall degree add one sub le ell
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Proofs.Exists_int_forall_degree_add_one_sub_le_ell
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
attribute [-simp] AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

universe u v

open IntermediateField

namespace HRIgenSol

private theorem Place_algebraTranscendental {K : Type u} {F : Type v} [Field K] [Field F] [Algebra
  K F]
    (v : AlgebraicCurve.Place K F) : Algebra.Transcendental K F := by
  rw [Algebra.transcendental_iff_not_isAlgebraic]
  intro halg
  apply v.ne_top'
  have hv := Valuation.integer.integers v.toValuationSubring.valuation
  let φ : K →+* v.toValuationSubring.valuation.integer :=
    (algebraMap K F).codRestrict _ fun a => by
      rw [ValuationSubring.integer_valuation]; exact v.algebraMap_mem' a
  have hcomp : (algebraMap v.toValuationSubring.valuation.integer F).comp φ = algebraMap K F :=
    RingHom.ext fun _ => rfl
  refine ValuationSubring.ext _ _ fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  obtain ⟨p, hp, hpx⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral
  have hx : IsIntegral v.toValuationSubring.valuation.integer x :=
    ⟨p.map φ, hp.map φ, by rw [Polynomial.eval₂_map, hcomp]; exact hpx⟩
  have hmem := hv.mem_of_integral hx
  rw [ValuationSubring.integer_valuation] at hmem
  exact hmem

private theorem algebraTranscendental_of_nonempty_place {K : Type u} {F : Type v} [Field K] [Field
  F]
    [Algebra K F] [h : Nonempty (AlgebraicCurve.Place K F)] : Algebra.Transcendental K F :=
  h.elim fun v => Place_algebraTranscendental v

section Tower

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

@[reducible] private noncomputable def ratFuncAlgebra (t : F) (htr : Transcendental K t) : Algebra
  (RatFunc K) F :=
  ((algebraMap K⟮t⟯ F).comp (RatFunc.algEquivOfTranscendental t htr).toAlgHom.toRingHom).toAlgebra

@[reducible] private noncomputable def ratFuncAlgebraAdjoin (t : F) (htr : Transcendental K t) :
    Algebra (RatFunc K) K⟮t⟯ :=
  (RatFunc.algEquivOfTranscendental t htr).toAlgHom.toRingHom.toAlgebra

private theorem isScalarTower (t : F) (htr : Transcendental K t) :
    letI := ratFuncAlgebra t htr
    IsScalarTower K (RatFunc K) F := by
  let := ratFuncAlgebra t htr
  refine IsScalarTower.of_algebraMap_eq fun k => ?_
  change algebraMap K F k =
    algebraMap K⟮t⟯ F (RatFunc.algEquivOfTranscendental t htr (algebraMap K (RatFunc K) k))
  rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

private theorem isScalarTower_adjoin (t : F) (htr : Transcendental K t) :
    letI := ratFuncAlgebra t htr
    letI := ratFuncAlgebraAdjoin t htr
    IsScalarTower (RatFunc K) K⟮t⟯ F := by
  let := ratFuncAlgebra t htr
  let := ratFuncAlgebraAdjoin t htr
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

private theorem finite_adjoin (t : F) (htr : Transcendental K t) :
    letI := ratFuncAlgebraAdjoin t htr
    Module.Finite (RatFunc K) K⟮t⟯ := by
  let := ratFuncAlgebraAdjoin t htr
  exact Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) K⟮t⟯)
    (RatFunc.algEquivOfTranscendental t htr).surjective

private theorem isSeparable_adjoin (t : F) (htr : Transcendental K t) :
    letI := ratFuncAlgebraAdjoin t htr
    Algebra.IsSeparable (RatFunc K) K⟮t⟯ := by
  let := ratFuncAlgebraAdjoin t htr
  refine ⟨fun y => ?_⟩
  obtain ⟨x, rfl⟩ := (RatFunc.algEquivOfTranscendental t htr).surjective y
  exact isSeparable_algebraMap x

private theorem finite (t : F) (htr : Transcendental K t) [FiniteDimensional K⟮t⟯ F] :
    letI := ratFuncAlgebra t htr
    FiniteDimensional (RatFunc K) F := by
  let := ratFuncAlgebra t htr
  let := ratFuncAlgebraAdjoin t htr
  have := isScalarTower_adjoin t htr
  have := finite_adjoin t htr
  exact Module.Finite.trans K⟮t⟯ F

private theorem isSeparable (t : F) (htr : Transcendental K t) [Algebra.IsSeparable K⟮t⟯ F] :
    letI := ratFuncAlgebra t htr
    Algebra.IsSeparable (RatFunc K) F := by
  let := ratFuncAlgebra t htr
  let := ratFuncAlgebraAdjoin t htr
  have := isScalarTower_adjoin t htr
  have := isSeparable_adjoin t htr
  exact Algebra.IsSeparable.trans (F := RatFunc K) (E := K⟮t⟯) (K := F)

end Tower

end HRIgenSol

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.exists_int_forall_degree_add_one_sub_le_ell
    (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F] :
    ∃ γ : ℤ, ∀ D : Divisor K F, Divisor.degree D + 1 - γ ≤ (ell D : ℤ) := by
  classical
  by_cases hP : Nonempty (Place K F)
  · have : Algebra.Transcendental K F := HRIgenSol.algebraTranscendental_of_nonempty_place
    obtain ⟨t, htr, hfd, hsep⟩ :=
      AlgebraicCurve.exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one (K :=
        K) (F := F)
        IsCurveOver.kaehler_free_rank_one.2
    let := HRIgenSol.ratFuncAlgebra t htr
    have := HRIgenSol.isScalarTower t htr
    have := HRIgenSol.finite t htr
    have := HRIgenSol.isSeparable t htr
    have : FiniteDimensional K (LSpace (0 : Divisor K F)) := finiteDimensional_lSpace_zero K F
    have hSGE : StichtenothGenusExists K F :=
      RationalFunctionField.stichtenothGenusExists_of_ratFunc_tower K F
    obtain ⟨γ, hγ⟩ := exists_genus_riemannIndex_of_stichtenothGenusExists hSGE
    refine ⟨γ, fun D => ?_⟩
    obtain ⟨-, hD⟩ := hγ D
    have h0 : (0 : ℤ) ≤ (indexOfSpecialty D : ℤ) := Int.natCast_nonneg _
    omega
  · have : IsEmpty (Place K F) := not_nonempty_iff.mp hP
    refine ⟨1, fun D => ?_⟩
    rw [Subsingleton.elim D 0, map_zero]
    have h0 : (0 : ℤ) ≤ (ell (0 : Divisor K F) : ℤ) := Int.natCast_nonneg _
    omega
end AlgebraicCurves.Geometry.Proofs.Exists_int_forall_degree_add_one_sub_le_ell
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
