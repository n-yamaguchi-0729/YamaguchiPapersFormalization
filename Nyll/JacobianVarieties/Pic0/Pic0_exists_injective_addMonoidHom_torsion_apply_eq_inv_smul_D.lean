/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_exists_injective_addMonoidHom_torsion_apply_eq_inv_smul_D.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Divisors.Divisor_inv_smul_D_eq_inv_smul_D_of_isPrincipal_sub
import Nyll.AlgebraicCurves.Divisors.Divisor_exists_eq_pow_and_eq_ord_of_inv_smul_D_eq_zero
import Nyll.AlgebraicCurves.FunctionFields.ConstantsAreBase_of_isAlgClosed_of_transcendental

/-!
# Logarithmic differentiation of torsion classes

Principal multiples of degree-zero divisor representatives define an additive map
from torsion classes to differentials. Separability and a nonzero differential
make this map injective; its value agrees with any principal-multiple witness.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.TorsionDlog
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance]
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp]
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp]
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

noncomputable section

open _root_.AlgebraicCurve
open _root_.KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve

namespace DlogRecipe

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_rep {p : ℕ} (x : Pic0.torsion K F p) :
    ∃ (E : Divisor.degZero (K := K) (F := F)) (g : F), Pic0.mk E = (x : Pic0 K F) ∧ g ≠ 0 ∧
      ∀ v : Place K F, (p : ℤ) * (E : Divisor K F) v = v.ord g := by
  obtain ⟨E, hE⟩ := Pic0.mk_surjective (x : Pic0 K F)
  have hx := Pic0.mem_torsion.mp x.2
  have hmk : (Pic0.mk ((p : ℤ) • E) : Pic0 K F) = 0 := by
    rw [← hE] at hx
    rw [Pic0.mk, QuotientAddGroup.mk_zsmul]
    exact hx
  rw [Pic0.mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hmk
  obtain ⟨g, hg, hEg⟩ := hmk
  refine ⟨E, g, hE, hg, fun v => ?_⟩
  rw [← hEg v]
  rfl

theorem hconst_of_isAlgClosed [IsAlgClosed K] (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] :
    ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → u ∈ (algebraMap K F).range := by
  intro u hu hord
  have hC : ConstantsAreBase K F := constantsAreBase_of_isAlgClosed_of_transcendental t ht
  have hmem : u ∈ LSpace (0 : Divisor K F) := by
    rw [mem_lSpace_iff_ord]
    exact Or.inr fun v => by rw [hord v, Finsupp.zero_apply, neg_zero]
  rw [ConstantsAreBase] at hC
  rw [hC] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc⟩

theorem isPrincipal_sub_of_mk_eq {E₁ E₂ : Divisor.degZero (K := K) (F := F)}
    (h : Pic0.mk E₁ = Pic0.mk E₂) :
      Divisor.IsPrincipal ((E₁ : Divisor K F) - (E₂ : Divisor K F)) := by
  rw [Pic0.mk, Pic0.mk, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf] at h
  exact h

theorem dlog_mul {g₁ g₂ : F} (h₁ : g₁ ≠ 0) (h₂ : g₂ ≠ 0) :
    (g₁ * g₂)⁻¹ • D K F (g₁ * g₂) = g₁⁻¹ • D K F g₁ + g₂⁻¹ • D K F g₂ := by
  rw [Derivation.leibniz, smul_add, smul_smul, smul_smul, add_comm]
  congr 1
  · congr 1
    field_simp
  · congr 1
    field_simp

variable [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
variable (t : F) (ht : Transcendental K t)
variable [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
variable (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F)
variable (hdt : D K F t ≠ 0)

/-- The logarithmic differential of a function witnessing a principal multiple of the class. -/
def dlogFun (x : Pic0.torsion K F p) : Ω[F⁄K] :=
  ((exists_rep x).choose_spec.choose)⁻¹ • D K F (exists_rep x).choose_spec.choose

include ht in
omit [Fact p.Prime] in
theorem dlogFun_eq (x : Pic0.torsion K F p) (E : Divisor.degZero (K := K) (F := F)) (g : F)
    (hEx : Pic0.mk E = (x : Pic0 K F)) (hg : g ≠ 0)
    (hEg : ∀ v : Place K F, (p : ℤ) * (E : Divisor K F) v = v.ord g) :
    dlogFun p x = g⁻¹ • D K F g := by
  obtain ⟨hE₀x, hg₀, hE₀g⟩ := (exists_rep x).choose_spec.choose_spec
  rw [dlogFun]
  refine Divisor.inv_smul_D_eq_inv_smul_D_of_isPrincipal_sub K F p (hconst_of_isAlgClosed t ht)
    _ _ (isPrincipal_sub_of_mk_eq (hE₀x.trans hEx.symm)) _ _ hg₀ hg hE₀g hEg

include ht in
omit [Fact p.Prime] in
theorem dlogFun_add (x y : Pic0.torsion K F p) : dlogFun p (x + y) = dlogFun p x + dlogFun p y := by
  obtain ⟨E₁, g₁, h₁x, hg₁, h₁⟩ := exists_rep x
  obtain ⟨E₂, g₂, h₂x, hg₂, h₂⟩ := exists_rep y
  rw [dlogFun_eq p t ht x E₁ g₁ h₁x hg₁ h₁, dlogFun_eq p t ht y E₂ g₂ h₂x hg₂ h₂,
    dlogFun_eq p t ht (x + y) (E₁ + E₂) (g₁ * g₂) ?_ (mul_ne_zero hg₁ hg₂) ?_, dlog_mul hg₁ hg₂]
  · rw [Pic0.mk_add, h₁x, h₂x]; rfl
  · intro v
    rw [AddSubgroup.coe_add, Finsupp.add_apply, mul_add, h₁ v, h₂ v, v.ord_mul hg₁ hg₂]

/-- The additive map on torsion classes obtained from logarithmic differentials. -/
def dlogHom : Pic0.torsion K F p →+ Ω[F⁄K] :=
  AddMonoidHom.mk' (dlogFun p) (dlogFun_add p t ht)

include hsep hdt in
theorem dlogHom_injective : Function.Injective (dlogHom p t ht) := by
  intro x y hxy
  rw [← sub_eq_zero] at hxy ⊢
  rw [← map_sub] at hxy
  set z := x - y
  obtain ⟨E, g, hEz, hg, hEg⟩ := exists_rep z
  have h0 : g⁻¹ • D K F g = 0 := by
    rw [← dlogFun_eq p t ht z E g hEz hg hEg]; exact hxy
  obtain ⟨h, hh, -, hEh⟩ := Divisor.exists_eq_pow_and_eq_ord_of_inv_smul_D_eq_zero K F p t hsep hdt
    (E : Divisor K F) g hg hEg h0
  apply Subtype.ext
  change (z : Pic0 K F) = 0
  rw [← hEz, Pic0.mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  exact ⟨h, hh, hEh⟩

end DlogRecipe

end AlgebraicCurve

end

open _root_.AlgebraicCurve in
open _root_.JacobianVarieties.Pic0.Proofs.TorsionDlog.AlgebraicCurve.DlogRecipe in
theorem _root_.AlgebraicCurve.Pic0.exists_injective_addMonoidHom_torsion_apply_eq_inv_smul_D
    (K F : Type*) [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F)
    (hdt : KaehlerDifferential.D K F t ≠ 0) :
    ∃ δ : Pic0.torsion K F p →+ Ω[F⁄K], Function.Injective δ ∧
      ∀ (x : Pic0.torsion K F p) (E : Divisor.degZero (K := K) (F := F)) (g : F),
        Pic0.mk E = (x : Pic0 K F) → g ≠ 0 →
        (∀ v : Place K F, (p : ℤ) * (E : Divisor K F) v = v.ord g) →
        δ x = g⁻¹ • KaehlerDifferential.D K F g :=
  ⟨dlogHom p t ht, dlogHom_injective p t ht hsep hdt,
    fun x E g hEx hg hEg => dlogFun_eq p t ht x E g hEx hg hEg⟩
end JacobianVarieties.Pic0.Proofs.TorsionDlog
end ProofImplementation

attribute [-instance]
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance]
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp]
  AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd
  AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply
  AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
attribute [-simp]
  AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
