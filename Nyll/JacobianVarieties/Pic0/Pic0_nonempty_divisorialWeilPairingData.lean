/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_nonempty_divisorialWeilPairingData.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.JacobianVarieties.WeilPairing.Divisorial
import Nyll.JacobianVarieties.Pic0.Pic0_torsion_exists_addMonoidHom_eval_eq_pairing
import Nyll.JacobianVarieties.Pic0.Pic0_torsion_move_of_forall_isRational
import Nyll.AlgebraicCurves.Geometry.WeilReciprocity
import Nyll.AlgebraicCurves.Places.Place_mem_range_algebraMap_of_forall_ord_eq_zero
import Nyll.AlgebraicCurves.Places.Place_isRational_iff_deg_eq_one
import Nyll.AlgebraicCurves.FunctionFields.FunctionField_exists_ratFuncAlgHom_apply_X_eq

/-!
# Divisorial Weil pairing data over an algebraically closed field of characteristic zero.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_nonempty_divisorialWeilPairingData
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance]
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp]
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp]
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

noncomputable section

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace WC7P
open _root_.AlgebraicCurve

private theorem transcendental_not_mem_range {K F : Type*} [Field K] [Field F] [Algebra K F]
    {j : F} (hj : Transcendental K j) : j ∉ Set.range (algebraMap K F) := by
  rintro ⟨c, rfl⟩
  exact hj (isAlgebraic_algebraMap c)

private theorem ratFuncAlgHom_fieldRange_eq_adjoin {K F : Type*} [Field K] [Field F]
    [Algebra K F] (φ : RatFunc K →ₐ[K] F) :
    φ.fieldRange = IntermediateField.adjoin K ({φ RatFunc.X} : Set F) := by
  have key : ∀ p : Polynomial K,
      φ (algebraMap (Polynomial K) (RatFunc K) p) = Polynomial.aeval (φ RatFunc.X) p := by
    intro p
    have h2 : φ.comp (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K))
        = Polynomial.aeval (φ RatFunc.X) := by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
        RatFunc.algebraMap_X, Polynomial.aeval_X]
    exact DFunLike.congr_fun h2 p
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    apply RatFunc.induction_on z
    intro p q hq
    change φ (algebraMap (Polynomial K) (RatFunc K) p
        / algebraMap (Polynomial K) (RatFunc K) q)
      ∈ IntermediateField.adjoin K ({φ RatFunc.X} : Set F)
    rw [map_div₀, key, key]
    have hmem : ∀ r : Polynomial K,
        Polynomial.aeval (φ RatFunc.X) r
          ∈ IntermediateField.adjoin K ({φ RatFunc.X} : Set F) := by
      intro r
      exact IntermediateField.algebra_adjoin_le_adjoin K _
        (Polynomial.aeval_mem_adjoin_singleton K _)
    exact div_mem (hmem p) (hmem q)
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact ⟨RatFunc.X, rfl⟩

private theorem finite_ratFunc_of_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : RatFunc K →ₐ[K] F) {j : F} (hX : φ RatFunc.X = j)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F) :
    @Module.Finite (RatFunc K) F _ _ (φ.toRingHom.toAlgebra).toModule := by
  let : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  change FiniteDimensional (RatFunc K) F
  have hE : φ.fieldRange = IntermediateField.adjoin K ({j} : Set F) := by
    rw [ratFuncAlgHom_fieldRange_eq_adjoin, hX]
  have hfdE : FiniteDimensional φ.fieldRange F := by rw [hE]; exact hfd
  let ε : RatFunc K ≃ₐ[K] φ.fieldRange := AlgEquiv.ofInjectiveField φ
  let : Algebra (RatFunc K) φ.fieldRange := ε.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower (RatFunc K) φ.fieldRange F :=
    IsScalarTower.of_algebraMap_eq fun z => rfl
  have : Module.Finite (RatFunc K) φ.fieldRange :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) φ.fieldRange) ε.surjective
  exact Module.Finite.trans (↥φ.fieldRange) F

private theorem nonempty_dwpd {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    [NeZero n] [HasPrincipalDivisors K F]
    (hrec : WeilReciprocity K F)
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → ∃ c : K, u = algebraMap K F c)
    (hrat : ∀ v : Place K F, v.IsRational) :
    Nonempty (DivisorialWeilPairingData K F n) := by
  obtain ⟨hom, hhom⟩ := Pic0.torsion.exists_addMonoidHom_eval_eq_pairing hrec hconst
    (fun x S => Pic0.torsion.move_of_forall_isRational hrat n x S)
  refine ⟨⟨fun x y => (Additive.toMul (hom x)) y, fun d => ?_,
    fun x S => Pic0.torsion.move_of_forall_isRational hrat n x S⟩⟩
  exact hhom d d.classLeft d.classRight
    ⟨d.degZeroLeft, d.coe_degZeroLeft, (d.coe_classLeft).symm⟩
    ⟨d.degZeroRight, d.coe_degZeroRight, (d.coe_classRight).symm⟩

end AlgebraicCurve.WC7P

open AlgebraicCurve.WC7P in
/-- A finite extension of a rational function field in characteristic zero admits
Weil pairing data. -/
theorem _root_.AlgebraicCurve.Pic0.nonempty_divisorialWeilPairingData (K F : Type*) [Field K]
    [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F)
    [IsCurveOver K F] (n : ℕ) [NeZero n] :
    Nonempty (DivisorialWeilPairingData K F n) := by
  classical
  obtain ⟨j, hjtr, hjfd⟩ := hfg
  have : FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F := hjfd
  have hrat : ∀ v : Place K F, v.IsRational := fun v =>
    (Place.isRational_iff_deg_eq_one v).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed v)
  have hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) →
      ∃ c : K, u = algebraMap K F c := by
    intro u _ hu
    obtain ⟨c, hc⟩ := RingHom.mem_range.mp
      (Place.mem_range_algebraMap_of_forall_ord_eq_zero j hjtr hu)
    exact ⟨c, hc.symm⟩
  obtain ⟨φ, hφX⟩ :=
    FunctionField.exists_ratFuncAlgHom_apply_X_eq (transcendental_not_mem_range hjtr)
  let : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  have : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have : FiniteDimensional (RatFunc K) F := finite_ratFunc_of_adjoin φ hφX hjfd
  exact nonempty_dwpd (weilReciprocity K F) hconst hrat

end
end JacobianVarieties.Pic0.Proofs.Pic0_nonempty_divisorialWeilPairingData
end ProofImplementation
