/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Differentials.Basic
import AlgebraicCurves.Differentials.Kaehler.KaehlerDifferential_span_D_eq_top_of_transcendental
import AlgebraicCurves.Differentials.Kaehler.KaehlerDifferential_D_ne_zero_of_transcendental
import AlgebraicCurves.FunctionFields.IsAlgebraic_adjoin_of_transcendental
import AlgebraicCurves.Places.Place_transcendental_of_ord_ne_zero
import AlgebraicCurves.Places.Place_exists_ord_eq_one
import Mathlib.FieldTheory.Perfect

/-!
# Place diff Coeff smul D eq
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_diffCoeff_smul_D_eq
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

noncomputable section
open KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace FF2R3
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
  [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]

include x in
private theorem isSeparable_adjoin (v : Place K F) {t : F} (ht : v.ord t ≠ 0) :
    Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F := by
  have : Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F :=
    AlgebraicCurve.isAlgebraic_adjoin_of_transcendental x (v.transcendental_of_ord_ne_zero ht)
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  infer_instance
include x in
theorem D_ne_zero_of_ord_ne_zero (v : Place K F) {t : F} (ht : v.ord t ≠ 0) : D K F t ≠ 0 :=
  haveI := isSeparable_adjoin x v ht
  KaehlerDifferential.D_ne_zero_of_transcendental K t (v.transcendental_of_ord_ne_zero ht)
include x in
theorem exists_eq_smul_D_of_ord_ne_zero (v : Place K F) {t : F} (ht : v.ord t ≠ 0) (ω : Ω[F⁄K]) :
    ∃ g : F, ω = g • D K F t := by
  have := isSeparable_adjoin x v ht
  have hspan := KaehlerDifferential.span_D_eq_top_of_transcendental K t
    (v.transcendental_of_ord_ne_zero ht)
  have hω : ω ∈ Submodule.span F {D K F t} := by rw [hspan]; trivial
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp hω
  exact ⟨g, hg.symm⟩
include x in
theorem diffCoeff_smul_D_of_ord_ne_zero (v : Place K F) {t : F} (ht : v.ord t ≠ 0) (ω : Ω[F⁄K]) :
    Place.diffCoeff t ω • D K F t = ω :=
  Place.diffCoeff_smul_D (exists_eq_smul_D_of_ord_ne_zero x v ht ω)
include x in
theorem diffCoeff_smul_of_ord_ne_zero (v : Place K F) {t : F} (ht : v.ord t ≠ 0) (g : F) :
    Place.diffCoeff t (g • D K F t) = g :=
  smul_left_injective F (D_ne_zero_of_ord_ne_zero x v ht)
    (Place.diffCoeff_smul_D ⟨g, rfl⟩)
include x in
theorem ordDiff_smul_D_uniformizer (v : Place K F) (g : F) :
    v.ordDiff (g • D K F v.uniformizer_alt) = v.ord g := by
  have h1 : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt v.exists_ord_eq_one
  rw [Place.ordDiff_def, diffCoeff_smul_of_ord_ne_zero x v (by rw [h1]; exact one_ne_zero)]
include x in
theorem ordDiff_zero (v : Place K F) : v.ordDiff 0 = 0 := by
  simpa using ordDiff_smul_D_uniformizer x v 0
include x in
theorem ordDiff_D_uniformizer (v : Place K F) : v.ordDiff (D K F v.uniformizer_alt) = 0 := by
  simpa using ordDiff_smul_D_uniformizer x v 1

end AlgebraicCurve.FF2R3

end

theorem _root_.AlgebraicCurve.Place.diffCoeff_smul_D_eq {K F : Type*} [Field K] [Field F] [Algebra
  K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K
      F) {t : F} (ht : v.ord t ≠ 0) (g : F) :
    AlgebraicCurve.Place.diffCoeff t (g • KaehlerDifferential.D K F t) = g :=
  AlgebraicCurve.FF2R3.diffCoeff_smul_of_ord_ne_zero x v ht g
end AlgebraicCurves.Places.Proofs.Place_diffCoeff_smul_D_eq
end ProofImplementation
