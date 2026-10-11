/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ord_algebraMap_eq_mul_ord_of_constant_extension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Places.Place_ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top

/-!
# Place ord algebra Map eq mul ord of constant extension
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ord_algebraMap_eq_mul_ord_of_constant_extension
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
attribute [-simp] AlgebraicCurve.Pic.baseChange_mk
  AlgebraicCurve.Place.forgetConstants_toValuationSubring
  AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants
  AlgebraicCurve.Place.extendConstants_toValuationSubring
  AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring
  AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.ord_algebraMap_eq_mul_ord_of_constant_extension
    {k K E F E' F' : Type*} [Field k] [Field K] [Field E] [Field F] [Field E'] [Field F']
    [Algebra k K] [Algebra.IsAlgebraic k K] [Algebra.IsSeparable k K]
    [Algebra k E] [Algebra k F] [Algebra E F] [IsScalarTower k E F]
    [Algebra K E'] [Algebra K F'] [Algebra E' F'] [IsScalarTower K E' F']
    [Algebra E E'] [Algebra F F'] [Algebra k E'] [Algebra k F']
    [IsScalarTower k K E'] [IsScalarTower k E E'] [IsScalarTower k K F'] [IsScalarTower k F F']
    (hsq : ∀ e : E, algebraMap F F' (algebraMap E F e) = algebraMap E' F' (algebraMap E E' e))
    (hgenE : Algebra.adjoin E (Set.range (algebraMap K E')) = ⊤)
    (hgenF : Algebra.adjoin F (Set.range (algebraMap K F')) = ⊤)
    (x : Place k F) (y : Place k E) (x' : Place K F') (y' : Place K E')
    (hx : x'.toValuationSubring.comap (algebraMap F F') = x.toValuationSubring)
    (hy : y'.toValuationSubring.comap (algebraMap E E') = y.toValuationSubring)
    (hx'y' : x'.toValuationSubring.comap (algebraMap E' F') = y'.toValuationSubring)
    (n : ℕ) (u : E) (hu : y.ord u = 1) (hn : x.ord (algebraMap E F u) = n) :
    ∀ f : E', x'.ord (algebraMap E' F' f) = n * y'.ord f := by
  classical
  have hF : ∀ g : F, x'.ord (algebraMap F F' g) = x.ord g :=
    AlgebraicCurve.Place.ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top hgenF x
      x' hx
  have hE : ∀ e : E, y'.ord (algebraMap E E' e) = y.ord e :=
    AlgebraicCurve.Place.ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top hgenE y
      y' hy
  set u' : E' := algebraMap E E' u with hu'
  have hu'1 : y'.ord u' = 1 := by rw [hu', hE, hu]
  have hu'n : x'.ord (algebraMap E' F' u') = n := by rw [hu', ← hsq, hF, hn]
  have hu'0 : u' ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hu'1; exact zero_ne_one hu'1
  have hmem : ∀ e : E', e ∈ y'.toValuationSubring → algebraMap E' F' e ∈ x'.toValuationSubring := by
    intro e he
    rw [← hx'y'] at he
    exact he
  let φ : y'.toValuationSubring →+* x'.toValuationSubring :=
    { toFun := fun e => ⟨algebraMap E' F' (e : E'), hmem _ e.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hunit : ∀ w : y'.toValuationSubringˣ, x'.ord (algebraMap E' F' ((w : y'.toValuationSubring)
    : E')) = 0 := by
    intro w
    have := x'.ord_coe_unit (Units.map (φ : y'.toValuationSubring →* x'.toValuationSubring) w)
    exact this
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible y'.toValuationSubring
  have hπ0 : (π : E') ≠ 0 := by
    intro h; exact hπ.ne_zero (Subtype.ext h)
  have hπF0 : algebraMap E' F' (π : E') ≠ 0 := (map_ne_zero _).mpr hπ0
  obtain ⟨w₀, hw₀⟩ := y'.exists_unit_mul_zpow hu'0 hπ
  rw [hu'1, zpow_one] at hw₀
  have hπn : x'.ord (algebraMap E' F' (π : E')) = n := by
    have h1 : x'.ord (algebraMap E' F' u') =
        x'.ord (algebraMap E' F' ((w₀ : y'.toValuationSubring) : E')) + x'.ord (algebraMap E' F' (π
          : E')) := by
      rw [hw₀, map_mul]
      exact x'.ord_mul ((map_ne_zero _).mpr (by simp)) hπF0
    rw [hunit w₀, zero_add, hu'n] at h1
    exact h1.symm
  intro f
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨w, hw⟩ := y'.exists_unit_mul_zpow hf hπ
  have hwF0 : algebraMap E' F' ((w : y'.toValuationSubring) : E') ≠ 0 := (map_ne_zero _).mpr
    (by simp)
  calc x'.ord (algebraMap E' F' f)
      = x'.ord (algebraMap E' F' ((w : y'.toValuationSubring) : E') * (algebraMap E' F' (π : E')) ^
        (y'.ord f)) := by
        conv_lhs => rw [hw]
        rw [map_mul, map_zpow₀]
    _ = x'.ord (algebraMap E' F' ((w : y'.toValuationSubring) : E')) + x'.ord ((algebraMap E' F' (π
      : E')) ^ (y'.ord f)) :=
        x'.ord_mul hwF0 (zpow_ne_zero _ hπF0)
    _ = (y'.ord f) * x'.ord (algebraMap E' F' (π : E')) := by rw [hunit w, zero_add, x'.ord_zpow]
    _ = n * y'.ord f := by rw [hπn, mul_comm]
end AlgebraicCurves.Places.Proofs.Place_ord_algebraMap_eq_mul_ord_of_constant_extension
end ProofImplementation
