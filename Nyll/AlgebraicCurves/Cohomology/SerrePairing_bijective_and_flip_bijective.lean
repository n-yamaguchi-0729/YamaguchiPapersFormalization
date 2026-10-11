/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_serrePairing_bijective_and_flip_bijective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Differentials.Order
import Nyll.AlgebraicCurves.Divisors.Canonical
import Nyll.AlgebraicCurves.Differentials.Residues.Basic
import Nyll.AlgebraicCurves.Differentials.Kaehler.Weil
import Nyll.AlgebraicCurves.Differentials.Regular
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.AlgebraicCurves.Cohomology.SerrePairing
import Nyll.AlgebraicCurves.Cohomology.Finite_H1_and_exists_linearEquiv_dual_H1_omegaSpace
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Exists_linearEquiv_regularDifferentials_omegaSpace_zero
import Nyll.AlgebraicCurves.Cohomology.CechH1ToH1_bijective
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Exists_genus_riemannIndex_of_isCurveOver
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Exists_riemannGenusReachedAt_of_bounded

/-!
# Serre Pairing bijective and flip bijective
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Proofs.SerrePairingBijectiveFlip
open _root_.AlgebraicCurve.Place in
attribute [-instance]
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
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
attribute [-simp] AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem finiteDimensional_lSpace_zero_of_constantsAreBase (hC : ConstantsAreBase K F) :
    FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := by
  have h : LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) := hC
  rw [h]
  infer_instance

theorem exists_riemannGenusReachedAt_of_constantsAreBase [PerfectField K] [Algebra.EssFiniteType K
  F]
    [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    ∃ (γ : ℤ) (D₀ : Divisor K F), RiemannGenusReachedAt γ D₀ := by
  have := finiteDimensional_lSpace_zero_of_constantsAreBase hC
  obtain ⟨γ, hγ⟩ := exists_genus_riemannIndex_of_isCurveOver (K := K) (F := F) hC
  refine exists_riemannGenusReachedAt_of_bounded ⟨γ - 1, fun D => ?_⟩
  have h := (hγ D).2
  have hi : (0 : ℤ) ≤ (indexOfSpecialty D : ℤ) := Int.natCast_nonneg _
  linarith

section Generic

variable [HasCanonicalLocalResidueKStar K F] [∀ v : Place K F, v.DCoordGenerates] [Nontrivial
  Ω[F⁄K]]
  [HasCanonicalDivisor (K := K) (F := F)] [HasPrincipalDivisors K F]

theorem serrePairing_apply_mk_eq_weilOfKaehler (hRT : ResidueTheorem K F) {S₀ S₁ : Set (Place K F)}
    (hcover : S₀ ∪ S₁ = Set.univ) (ω : ↥(regularDifferentials K F)) (hω : (ω : Ω[F⁄K]) ≠ 0)
    (f : ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F))) :
    serrePairing hRT hcover ω (Submodule.Quotient.mk f)
      = weilOfKaehler K F hω ⟨((extendOffChart K S₀ (f : F) : ↥(repartitions K F)) : Place K F → F),
          coe_extendOffChart_mem_adeleSpace S₀ (f : F)⟩ := by
  rw [serrePairing_apply_mk, residueSumOffChart_def, weilOfKaehler_apply]

theorem serrePairing_zero_left_apply (hRT : ResidueTheorem K F) {S₀ S₁ : Set (Place K F)}
    (hcover : S₀ ∪ S₁ = Set.univ) (x : cechH1 S₀ S₁ (0 : Divisor K F)) :
    serrePairing hRT hcover 0 x = 0 := by
  rw [map_zero, LinearMap.zero_apply]

end Generic

theorem serrePairing_bijective_and_flip_bijective' {K : Type*} {F : Type*} [Field K] [Field F]
  [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [HasCanonicalLocalResidueKStar K F]
    (hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁) :
    Function.Bijective (serrePairing hRT hcover) ∧
      Function.Bijective (serrePairing hRT hcover).flip := by
  classical
  have := finiteDimensional_lSpace_zero_of_constantsAreBase hC
  obtain ⟨γ, D₀, hγ⟩ := exists_riemannGenusReachedAt_of_constantsAreBase (K := K) (F := F) hC
  have hι : Function.Bijective (cechH1ToH1 hcover (0 : Divisor K F)) :=
    cechH1ToH1_bijective hγ hcover h₀ h₁ 0
  let ιe : cechH1 S₀ S₁ (0 : Divisor K F) ≃ₗ[K] H1 (0 : Divisor K F) :=
    LinearEquiv.ofBijective _ hι
  obtain ⟨hfin, e₀, he₀⟩ := finite_H1_and_exists_linearEquiv_dual_H1_omegaSpace (K := K) (F := F)
    hC 0
  obtain ⟨e₂, he₂⟩ := exists_linearEquiv_regularDifferentials_omegaSpace_zero (K := K) (F := F) hC
    hRT
  let E : ↥(regularDifferentials K F) ≃ₗ[K] Module.Dual K (cechH1 S₀ S₁ (0 : Divisor K F)) :=
    e₂.trans (e₀.symm.trans ιe.dualMap)
  have key : ∀ (ω : ↥(regularDifferentials K F)) (x : cechH1 S₀ S₁ (0 : Divisor K F)),
      serrePairing hRT hcover ω x = E ω x := by
    intro ω x
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hR : E ω (Submodule.Quotient.mk f)
        = (e₂ ω : Module.Dual K ↥(adeleSpace K F))
            ⟨((extendOffChart K S₀ (f : F) : ↥(repartitions K F)) : Place K F → F),
              coe_extendOffChart_mem_adeleSpace S₀ (f : F)⟩ := by
      change (ιe.dualMap (e₀.symm (e₂ ω))) (Submodule.Quotient.mk f) = _
      rw [LinearEquiv.dualMap_apply, LinearEquiv.ofBijective_apply, cechH1ToH1_mk]
      have h := he₀ (e₀.symm (e₂ ω))
        ⟨((extendOffChart K S₀ (f : F) : ↥(repartitions K F)) : Place K F → F),
          coe_extendOffChart_mem_adeleSpace S₀ (f : F)⟩ (extendOffChart K S₀ (f : F)).2
      rw [LinearEquiv.apply_symm_apply] at h
      rw [h]
    rw [hR]
    rcases eq_or_ne (ω : Ω[F⁄K]) 0 with hω | hω
    · have hω' : ω = 0 := Subtype.ext hω
      rw [hω', serrePairing_zero_left_apply, map_zero, Submodule.coe_zero, LinearMap.zero_apply]
    · rw [serrePairing_apply_mk_eq_weilOfKaehler hRT hcover ω hω, he₂ ω hω]
  have hfun : ⇑(serrePairing hRT hcover) = ⇑E :=
    funext fun ω => LinearMap.ext fun x => key ω x
  have hleft : Function.Bijective (serrePairing hRT hcover) := by
    rw [hfun]
    exact E.bijective
  refine ⟨hleft, ?_⟩
  have : Module.Finite K (H1 (0 : Divisor K F)) := hfin
  have : Module.Finite K (cechH1 S₀ S₁ (0 : Divisor K F)) := Module.Finite.equiv ιe.symm
  have : Module.Finite K ↥(regularDifferentials K F) := Module.Finite.equiv E.symm
  have hinj : Function.Injective (serrePairing hRT hcover).flip := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hall : ∀ φ : Module.Dual K (H1 (0 : Divisor K F)), φ (ιe x) = 0 := by
      intro φ
      let ω := (e₂.trans e₀.symm).symm φ
      have h1 : serrePairing hRT hcover ω x = 0 := by
        rw [← LinearMap.flip_apply, hx, LinearMap.zero_apply]
      rw [key ω x] at h1
      have h2 : E ω x = φ (ιe x) := by
        change (ιe.dualMap (e₀.symm (e₂ ((e₂.trans e₀.symm).symm φ)))) x = φ (ιe x)
        rw [LinearEquiv.dualMap_apply]
        congr 1
        change (e₂.trans e₀.symm) ((e₂.trans e₀.symm).symm φ) = φ
        exact LinearEquiv.apply_symm_apply _ φ
      rw [← h2]
      exact h1
    have hx0 : ιe x = 0 := (Module.forall_dual_apply_eq_zero_iff K (ιe x)).mp hall
    exact ιe.injective (hx0.trans (LinearEquiv.map_zero ιe).symm)
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj |> fun hsurj =>
    ⟨hinj, hsurj⟩
  rw [Subspace.dual_finrank_eq, E.finrank_eq, Subspace.dual_finrank_eq]

end AlgebraicCurve

open _root_.AlgebraicCurve
  _root_.AlgebraicCurves.Cohomology.Proofs.SerrePairingBijectiveFlip.AlgebraicCurve in
theorem _root_.AlgebraicCurve.serrePairing_bijective_and_flip_bijective {K : Type*} {F : Type*}
  [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [HasCanonicalLocalResidueKStar K F]
    (hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁) :
    Function.Bijective (serrePairing hRT hcover) ∧
      Function.Bijective (serrePairing hRT hcover).flip :=
  serrePairing_bijective_and_flip_bijective' hC hRT hcover h₀ h₁
end AlgebraicCurves.Cohomology.Proofs.SerrePairingBijectiveFlip
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
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
