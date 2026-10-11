/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_weilCanonical_riemannRoch.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Cohomology.RiemannRoch.StichtenothGenusExists_of_isCurveOver
import AlgebraicCurves.Differentials.WeilDifferentialRankOne_of_isCurveOver
import AlgebraicCurves.Cohomology.RiemannRoch.IndexOfSpecialty_eq_of_genusReached
import AlgebraicCurves.Cohomology.RiemannRoch.IndexOfSpecialty_eq_ell_sub_of_rankOne_max
import AlgebraicCurves.Cohomology.IndexOfSpecialty_eq_finrank_H1
import AlgebraicCurves.Cohomology.RiemannRoch.Ell_eq_zero_of_degree_neg
import AlgebraicCurves.Cohomology.RiemannRoch.Mul_mem_lSpace_add
import AlgebraicCurves.Geometry.One_le_deg
import AlgebraicCurves.Divisors.Divisor_degree_nonneg_of_nonneg

/-!
# Exists weil Canonical riemann Roch
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.Exists_weilCanonical_riemannRoch
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace WeilCanonicalRRSol
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem self_mem_lSpace_neg {z : F} {P : Divisor K F} (hP : ∀ v, P v = v.ord z) :
    z ∈ LSpace (-P) := by
  rw [mem_lSpace_iff_ord]
  exact Or.inr fun v => by simp [hP v]

theorem inv_mem_lSpace {z : F} {P : Divisor K F} (hP : ∀ v, P v = v.ord z) :
    z⁻¹ ∈ LSpace P := by
  rw [mem_lSpace_iff_ord]
  exact Or.inr fun v => by simp [Place.ord_inv, hP v]

theorem ell_add_eq_of_ord_eq {z : F} (hz : z ≠ 0) {P : Divisor K F}
    (hP : ∀ v, P v = v.ord z) (A : Divisor K F) : ell (A + P) = ell A := by
  have h1 : ∀ f : F, f ∈ LSpace (A + P) → f * z ∈ LSpace A := fun f hf => by
    have := mul_mem_lSpace_add hf (self_mem_lSpace_neg hP)
    rwa [add_neg_cancel_right] at this
  have h2 : ∀ g : F, g ∈ LSpace A → g * z⁻¹ ∈ LSpace (A + P) := fun g hg =>
    mul_mem_lSpace_add hg (inv_mem_lSpace hP)
  let e : LSpace (A + P) ≃ₗ[K] LSpace A :=
    { toFun := fun f => ⟨f.1 * z, h1 f.1 f.2⟩
      map_add' := fun f g => by
        ext
        simp [add_mul]
      map_smul' := fun c f => by
        ext
        simp
      invFun := fun g => ⟨g.1 * z⁻¹, h2 g.1 g.2⟩
      left_inv := fun f => by
        ext
        simp [mul_inv_cancel_right₀ hz]
      right_inv := fun g => by
        ext
        simp [inv_mul_cancel_right₀ hz] }
  exact e.finrank_eq

theorem degree_eq_zero_of_ord_eq [HasPrincipalDivisors K F] {z : F} (hz : z ≠ 0)
    {P : Divisor K F} (hP : ∀ v, P v = v.ord z) : Divisor.degree P = 0 := by
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) z hz
  have : D = P := Finsupp.ext fun v => by rw [hD v, hP v]
  rwa [this] at hdeg

theorem degree_pos_of_nonneg_of_ne_zero [IsCurveOver K F] {E : Divisor K F} (hE : 0 ≤ E)
    (hE0 : E ≠ 0) : 0 < Divisor.degree E := by
  classical
  have hEnn : ∀ w, 0 ≤ E w := fun w => by simpa using (Finsupp.le_def.mp hE) w
  obtain ⟨v, hv⟩ : ∃ v, E v ≠ 0 := by
    by_contra h
    push Not at h
    exact hE0 (Finsupp.ext h)
  have hEv : 1 ≤ E v := by
    have := hEnn v
    omega
  have hsplit : E = Finsupp.single v (E v) + Finsupp.erase v E :=
    (Finsupp.single_add_erase v E).symm
  have herase : ∀ w, 0 ≤ Finsupp.erase v E w := fun w => by
    rw [Finsupp.erase_apply]
    split_ifs
    · exact le_rfl
    · exact hEnn w
  have h1 : 0 ≤ Divisor.degree (Finsupp.erase v E) := Divisor.degree_nonneg_of_nonneg herase
  have h2 : (1 : ℤ) ≤ v.deg := by exact_mod_cast one_le_deg v
  rw [hsplit, map_add, Divisor.degree_single]
  nlinarith

theorem degree_lt_of_lt [IsCurveOver K F] {D E : Divisor K F} (h : D < E) :
    Divisor.degree D < Divisor.degree E := by
  have h1 : 0 ≤ E - D := by
    refine Finsupp.le_def.mpr fun w => ?_
    have := (Finsupp.le_def.mp h.le) w
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_sub, Pi.sub_apply]
    linarith
  have h2 : E - D ≠ 0 := sub_ne_zero.mpr (ne_of_gt h)
  have := degree_pos_of_nonneg_of_ne_zero h1 h2
  rw [map_sub] at this
  linarith

theorem adeleBdd_sup_le (A B : Divisor K F) :
    adeleBdd (A ⊔ B) ≤ adeleBdd A ⊔ adeleBdd B := by
  classical
  intro x hx
  let y : Place K F → F := fun v => if B v ≤ A v then x v else 0
  have hy : y ∈ adeleBdd A := fun v => by
    simp only [y]
    split_ifs with h
    · have := hx v
      rwa [Finsupp.sup_apply, sup_eq_left.mpr h] at this
    · rw [map_zero]
      exact zero_le
  have hz : x - y ∈ adeleBdd B := fun v => by
    simp only [Pi.sub_apply, y]
    split_ifs with h
    · rw [sub_self, map_zero]
      exact zero_le
    · have := hx v
      rw [Finsupp.sup_apply, sup_eq_right.mpr (not_le.mp h).le] at this
      rwa [sub_zero]
  have hx' : x = y + (x - y) := by abel
  rw [hx']
  exact Submodule.add_mem_sup hy hz

theorem mem_omegaSpace_sup {A B : Divisor K F} {φ : Module.Dual K (adeleSpace K F)}
    (hA : φ ∈ omegaSpace A) (hB : φ ∈ omegaSpace B) : φ ∈ omegaSpace (A ⊔ B) := by
  rw [omegaSpace, Submodule.mem_dualAnnihilator]
  intro w hw
  obtain ⟨b, hb, g, hg, rfl⟩ := Submodule.mem_sup.mp hw
  have hb' : (b : Place K F → F) ∈ adeleBdd A ⊔ adeleBdd B :=
    adeleBdd_sup_le A B (Submodule.mem_comap.mp hb)
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hb'
  have hbeq : b = ⟨s, adeleBdd_le_adeleSpace hs⟩ + ⟨t, adeleBdd_le_adeleSpace ht⟩ :=
    Subtype.ext hst.symm
  rw [map_add, hbeq, map_add, omegaSpace_vanishBdd hA (α := ⟨s, _⟩) hs,
    omegaSpace_vanishBdd hB (α := ⟨t, _⟩) ht,
    omegaSpace_vanishGlobal hA (Submodule.mem_comap.mp hg)]
  simp

theorem main [PerfectField K] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hC : ConstantsAreBase K F) :
    ∃ W : Divisor K F, ∀ D : Divisor K F,
      (ell D : ℤ) - (ell (W - D) : ℤ) = Divisor.degree D + 1 - (genusFF K F : ℤ) := by
  classical
  obtain ⟨hne, hfin, γ, D₀, hR⟩ := stichtenothGenusExists_of_isCurveOver hC
  have : Nonempty (Place K F) := hne
  have : FiniteDimensional K (LSpace (0 : Divisor K F)) := hfin
  have hidx : ∀ D : Divisor K F,
      Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D) ∧
        (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - γ) :=
    fun D => indexOfSpecialty_eq_of_genusReached hR D
  have hg0 : indexOfSpecialty (0 : Divisor K F) = genusFF K F := indexOfSpecialty_eq_finrank_H1 0
  have hγ : (genusFF K F : ℤ) = γ := by
    have h := (hidx 0).2
    rw [hg0, ell_zero_eq_one_of_constantsAreBase hC, map_zero] at h
    push_cast at h
    linarith
  have hγnn : (0 : ℤ) ≤ γ := by
    rw [← hγ]
    positivity
  have hfinΩ : ∀ E : Divisor K F, Module.Finite K (omegaSpace E) := fun E => by
    have := (hidx E).1
    exact Module.Finite.equiv (omegaSpaceEquivIndexDual E).symm
  have hpos : ∀ (E : Divisor K F) (ψ : Module.Dual K (adeleSpace K F)),
      ψ ∈ omegaSpace E → ψ ≠ 0 → 1 ≤ indexOfSpecialty E := by
    intro E ψ hψ hψ0
    have := hfinΩ E
    rw [← finrank_omegaSpace_eq_indexOfSpecialty, Nat.one_le_iff_ne_zero, Ne,
      Submodule.finrank_eq_zero]
    intro hbot
    rw [hbot] at hψ
    exact hψ0 ((Submodule.mem_bot K).mp hψ)
  have hshift : ∀ (E P : Divisor K F) (z : F), z ≠ 0 → (∀ v, P v = v.ord z) →
      indexOfSpecialty (E + P) = indexOfSpecialty E := by
    intro E P z hz hP
    have h1 := (hidx (E + P)).2
    have h2 := (hidx E).2
    rw [ell_add_eq_of_ord_eq hz hP, map_add, degree_eq_zero_of_ord_eq hz hP, add_zero] at h1
    exact_mod_cast h1.trans h2.symm
  have hzero : ∀ E : Divisor K F, D₀ ≤ E → indexOfSpecialty E = 0 := by
    intro E hE
    have h0 : indexOfSpecialty D₀ = 0 := by
      have h := (hidx D₀).2
      have := hR.eq
      have : (indexOfSpecialty D₀ : ℤ) = 0 := by linarith
      exact_mod_cast this
    have hbot : omegaSpace D₀ = ⊥ := by
      have := hfinΩ D₀
      rw [← Submodule.finrank_eq_zero, finrank_omegaSpace_eq_indexOfSpecialty, h0]
    have hle : omegaSpace E ≤ ⊥ := hbot ▸ omegaSpace_antitone hE
    have := hfinΩ E
    rw [← finrank_omegaSpace_eq_indexOfSpecialty, Submodule.finrank_eq_zero]
    exact le_bot_iff.mp hle
  let v₀ : Place K F := Classical.arbitrary _
  set D₁ : Divisor K F := -Finsupp.single v₀ 2 with hD₁
  have hdegD₁ : Divisor.degree D₁ = -(2 * (v₀.deg : ℤ)) := by
    rw [hD₁, map_neg, Divisor.degree_single]
  have hv₀ : (1 : ℤ) ≤ v₀.deg := by exact_mod_cast one_le_deg v₀
  have hellD₁ : ell D₁ = 0 := ell_eq_zero_of_degree_neg (by rw [hdegD₁]; linarith)
  have hiD₁ : 1 ≤ indexOfSpecialty D₁ := by
    have h := (hidx D₁).2
    rw [hellD₁, hdegD₁] at h
    have : (1 : ℤ) ≤ indexOfSpecialty D₁ := by
      push_cast at h
      linarith
    exact_mod_cast this
  obtain ⟨φ, hφD₁, hφ0⟩ : ∃ φ ∈ omegaSpace D₁, φ ≠ 0 := by
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    intro hbot
    have h := finrank_omegaSpace_eq_indexOfSpecialty D₁
    rw [hbot, finrank_bot] at h
    omega
  have hbound : ∀ E : Divisor K F, φ ∈ omegaSpace E →
      Divisor.degree E < Divisor.degree D₀ + γ := by
    intro E hE
    by_contra hle
    push Not at hle
    have h1 : 1 ≤ ell (E - D₀) := by
      have := hR.isMax (E - D₀)
      rw [map_sub] at this
      have : (1 : ℤ) ≤ ell (E - D₀) := by linarith
      exact_mod_cast this
    obtain ⟨z, hzmem, hz0⟩ : ∃ z ∈ LSpace (E - D₀), z ≠ 0 := by
      apply Submodule.exists_mem_ne_zero_of_ne_bot
      intro hbot
      have : ell (E - D₀) = 0 := by
        change Module.finrank K (LSpace (E - D₀)) = 0
        rw [hbot, finrank_bot]
      omega
    obtain ⟨P, hP, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) z hz0
    have hEP : D₀ ≤ E + P := by
      refine Finsupp.le_def.mpr fun v => ?_
      have h := (mem_lSpace_iff_ord.mp hzmem).resolve_left hz0 v
      rw [← hP v] at h
      simp only [Finsupp.coe_sub, Pi.sub_apply] at h
      simp only [Finsupp.coe_add, Pi.add_apply]
      linarith
    have h2 : indexOfSpecialty (E + P) = 0 := hzero (E + P) hEP
    have h3 : 1 ≤ indexOfSpecialty E := hpos E φ hE hφ0
    rw [hshift E P z hz0 hP] at h2
    omega
  obtain ⟨m, ⟨W, hφW, hWm⟩, hmax⟩ := Int.exists_greatest_of_bdd
      (P := fun n : ℤ => ∃ E : Divisor K F, φ ∈ omegaSpace E ∧ Divisor.degree E = n)
      ⟨Divisor.degree D₀ + γ, fun n ⟨E, hE, hEn⟩ => hEn ▸ (hbound E hE).le⟩
      ⟨Divisor.degree D₁, D₁, hφD₁, rfl⟩
  have hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W := by
    intro E hE
    by_contra hEW
    have hsup : φ ∈ omegaSpace (E ⊔ W) := mem_omegaSpace_sup hE hφW
    have hlt : W < E ⊔ W := right_lt_sup.mpr hEW
    have h1 := degree_lt_of_lt hlt
    have h2 := hmax _ ⟨E ⊔ W, hsup, rfl⟩
    rw [← hWm] at h2
    linarith
  have hrank : WeilDifferentialRankOne K F := weilDifferentialRankOne_of_isCurveOver hC
  refine ⟨W, fun D => ?_⟩
  have hdual : indexOfSpecialty D = ell (W - D) :=
    indexOfSpecialty_eq_ell_sub_of_rankOne_max hrank hφW hφ0 hWmax D
  have h := (hidx D).2
  rw [hdual] at h
  rw [hγ]
  linarith

end AlgebraicCurve.WeilCanonicalRRSol

theorem _root_.AlgebraicCurve.exists_weilCanonical_riemannRoch
    (K F : Type*) [Field K] [PerfectField K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hC : AlgebraicCurve.ConstantsAreBase K F) :
    ∃ W : AlgebraicCurve.Divisor K F, ∀ D : AlgebraicCurve.Divisor K F,
      (AlgebraicCurve.ell D : ℤ) - (AlgebraicCurve.ell (W - D) : ℤ) =
        AlgebraicCurve.Divisor.degree D + 1 - (AlgebraicCurve.genusFF K F : ℤ) :=
  AlgebraicCurve.WeilCanonicalRRSol.main hC
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.Exists_weilCanonical_riemannRoch
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
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
