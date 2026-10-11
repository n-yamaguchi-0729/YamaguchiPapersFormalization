/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_finiteDimensional_lSpace_zero_and_ell_zero_eq_one_of_isAlgClosed_of_transcendental.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.FunctionFields.IsCurveOver_of_isAlgClosed_of_transcendental
import AlgebraicCurves.Places.Exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
import AlgebraicCurves.Cohomology.RiemannRoch.FiniteDimensional_lSpace_zero

/-!
# Finite Dimensional l Space zero and ell zero eq one of is Alg Closed of transcendental
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.FiniteDimLSpaceZeroEllZeroOneAlg
open _root_.AlgebraicCurve.Place in
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
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
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
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

open AlgebraicCurve
open scoped IntermediateField

namespace E97cEllZero

theorem main (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    FiniteDimensional k ↥(LSpace (0 : Divisor k F)) ∧ ell (0 : Divisor k F) = 1 := by
  classical
  have := hfin
  have : IsCurveOver k F := AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx
  let e := RatFunc.algEquivOfTranscendental x hx
  let : Algebra (RatFunc k) k⟮x⟯ := e.toAlgHom.toRingHom.toAlgebra
  let : Algebra (RatFunc k) F := ((algebraMap k⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have : IsScalarTower (RatFunc k) k⟮x⟯ F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k (RatFunc k) F :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap k F r = algebraMap k⟮x⟯ F (e (algebraMap k (RatFunc k) r))
      rw [AlgEquiv.commutes]
      exact IsScalarTower.algebraMap_apply k k⟮x⟯ F r
  have : Module.Finite (RatFunc k) k⟮x⟯ :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc k) k⟮x⟯) e.surjective
  have : Module.Finite (RatFunc k) F := Module.Finite.trans k⟮x⟯ F
  have : Algebra.EssFiniteType (Polynomial k) (RatFunc k) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc k) (nonZeroDivisors (Polynomial k))
  have : Algebra.EssFiniteType k (RatFunc k) := Algebra.EssFiniteType.comp k (Polynomial k)
    (RatFunc k)
  have : Algebra.EssFiniteType (RatFunc k) F := inferInstance
  have : Algebra.EssFiniteType k F := Algebra.EssFiniteType.comp k (RatFunc k) F
  have : Nonempty (Place k F) := by
    obtain ⟨S, -, hsum⟩ := AlgebraicCurve.exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed k x
      hx hfin
    by_contra h
    have hS : S = ∅ := Finset.eq_empty_of_forall_notMem fun v _ => h ⟨v⟩
    rw [hS, Finset.sum_empty] at hsum
    have hpos : 0 < Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F :=
      Module.finrank_pos
    omega
  have hfd : FiniteDimensional k ↥(LSpace (0 : Divisor k F)) :=
    AlgebraicCurve.finiteDimensional_lSpace_zero k F
  refine ⟨hfd, ?_⟩
  have hmem0 : ∀ {y : F}, y ∈ LSpace (0 : Divisor k F) ↔ y = 0 ∨ ∀ v : Place k F, 0 ≤ v.ord y := by
    intro y
    rw [mem_lSpace_iff_ord]
    simp
  let L0 : Subalgebra k F :=
    { carrier := LSpace (0 : Divisor k F)
      mul_mem' := fun {a b} ha hb => by
        rcases eq_or_ne a 0 with rfl | ha0
        · simp
        rcases eq_or_ne b 0 with rfl | hb0
        · simp
        have ha' := (hmem0.mp ha).resolve_left ha0
        have hb' := (hmem0.mp hb).resolve_left hb0
        exact hmem0.mpr (Or.inr fun v =>
          by rw [Place.ord_mul v ha0 hb0]; exact add_nonneg (ha' v) (hb' v))
      add_mem' := fun ha hb => (LSpace (0 : Divisor k F)).add_mem ha hb
      algebraMap_mem' := fun c => algebraMap_mem_lSpace_zero c }
  have hL0 : L0.toSubmodule = LSpace (0 : Divisor k F) := rfl
  have hfg : L0.toSubmodule.FG := by
    rw [hL0]
    exact Module.Finite.iff_fg.mp hfd
  have hconst : ∀ y ∈ LSpace (0 : Divisor k F), y ∈ (algebraMap k F).range := by
    intro y hy
    have hint : IsIntegral k y := IsIntegral.of_mem_of_fg L0 hfg y hy
    exact minpoly.mem_range_of_degree_eq_one k y (IsAlgClosed.degree_eq_one_of_irreducible k
      (minpoly.irreducible hint))
  have hC : ConstantsAreBase k F := by
    apply le_antisymm
    · intro y hy
      obtain ⟨c, rfl⟩ := hconst y hy
      exact ⟨c, rfl⟩
    · rintro _ ⟨c, rfl⟩
      exact algebraMap_mem_lSpace_zero c
  exact ell_zero_eq_one_of_constantsAreBase hC

end E97cEllZero

end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.FiniteDimLSpaceZeroEllZeroOneAlg

section PublicStatement

open _root_.AlgebraicCurve
open scoped IntermediateField
open _root_.AlgebraicCurves.Cohomology.RiemannRoch.Proofs.FiniteDimLSpaceZeroEllZeroOneAlg

namespace AlgebraicCurve

theorem finiteDimensional_lSpace_zero_and_ell_zero_eq_one_of_isAlgClosed_of_transcendental
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    FiniteDimensional k ↥(LSpace (0 : Divisor k F)) ∧ ell (0 : Divisor k F) = 1 :=
  E97cEllZero.main k x hx hfin

end AlgebraicCurve

end PublicStatement
end ProofImplementation
