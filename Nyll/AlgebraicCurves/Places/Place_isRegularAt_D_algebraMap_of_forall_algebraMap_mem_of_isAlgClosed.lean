/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_isRegularAt_D_algebraMap_of_forall_algebraMap_mem_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Differentials.Polar
import Nyll.AlgebraicCurves.Differentials.LocalUnitDerivativeRegular_of_isCurveOver
import Nyll.AlgebraicCurves.Differentials.DCoordGenerates_of_isCurveOver

/-!
# Place is Regular At D algebra Map of forall algebra Map mem of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_isRegularAt_D_algebraMap_of_forall_algebraMap_mem_of_isAlgClosed
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

open _root_.AlgebraicCurve
open _root_.KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace GenericPlaceB1
open _root_.AlgebraicCurve

variable {L E : Type*} [Field L] [Field E] [Algebra L E] (v : Place L E)

theorem ord_nonneg_of_mem {f : E} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hf' : f = ((u : v.toValuationSubring) : E) * ((π : E) ^ (n : ℤ)) := by
    have := congrArg (fun z : v.toValuationSubring => (z : E)) hu
    simpa [zpow_natCast] using this
  rw [hf', v.ord_unit_smul_zpow u hπ]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg {f : E} (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, ← Int.toNat_of_nonneg h, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem ord_eq_zero_of_mem_of_inv_mem {f : E} (h1 : f ∈ v.toValuationSubring) (h2 : f⁻¹ ∈
  v.toValuationSubring) :
    v.ord f = 0 := by
  have a := ord_nonneg_of_mem v h1
  have b := ord_nonneg_of_mem v h2
  rw [v.ord_inv] at b
  omega

end AlgebraicCurve.GenericPlaceB1

open _root_.AlgebraicCurve AlgebraicCurve AlgebraicCurve.GenericPlaceB1 KaehlerDifferential in
theorem _root_.AlgebraicCurve.Place.isRegularAt_D_algebraMap_of_forall_algebraMap_mem_of_isAlgClosed
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    [Algebra.EssFiniteType K' F']
    (_hsep : ∃ x₀ : F, Transcendental K x₀ ∧ FiniteDimensional (IntermediateField.adjoin K ({x₀} :
      Set F)) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin K ({x₀} : Set F)) F)
    (_hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (_hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (w : Place K' F') (hw : ∀ f : F, algebraMap F F' f ∈ w.toValuationSubring) (x : F) :
    w.IsRegularAt (KaehlerDifferential.D K' F' (algebraMap F F' x)) := by
  have : ∀ w' : Place K' F', w'.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, map_zero]
    exact w.isRegularAt_zero
  set u := algebraMap F F' x with hu
  have hu0 : u ≠ 0 := (map_ne_zero _).mpr hx
  have hord : w.ord u = 0 :=
    ord_eq_zero_of_mem_of_inv_mem w (hw x) (by rw [hu, ← map_inv₀]; exact hw _)
  have hDu : D K' F' u = w.differentialCoeff (D K' F' u) • w.dCoord :=
    (w.differentialCoeff_smul_dCoord _).symm
  rcases AlgebraicCurve.localUnitDerivativeRegular_of_isCurveOver w u hu0 hord with h0 | hnn
  · exact ⟨0, zero_mem _, by rw [hDu, h0]⟩
  · refine ⟨w.differentialCoeff (D K' F' u), ?_, hDu⟩
    rcases eq_or_ne (w.differentialCoeff (D K' F' u)) 0 with hz | hz
    · rw [hz]; exact zero_mem _
    · exact mem_of_ord_nonneg w hz hnn

end Place_isRegularAt_D_algebraMap_of_forall_algebraMap_mem_of_isAlgClosed
end AlgebraicCurves.Places.Proofs
end ProofImplementation
