/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.DedekindDomain.Factorization
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Util.WithWeakNamespace

/-!
# RationalFunctionField subsingleton setOf forall ne ofHeightOneSpectrum

The places of a rational function field outside the polynomial height-one spectrum form a
subsingleton.
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs
namespace RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum

noncomputable section

open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.adicValuation_valuationSubring' :
    v.adicValuation.valuationSubring = v.toValuationSubring := by
  ext x
  rw [Valuation.mem_valuationSubring_iff]
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    exact a.2
  · intro hx
    exact v.heightOneSpectrum.valuation_le_one (⟨x, hx⟩ : v.toValuationSubring)

open _root_.AlgebraicCurve.Place
private theorem _root_.AlgebraicCurve.Place.mem_iff_adicValuation_le_one' {f : F} :
    f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 := by
  rw [← v.adicValuation_valuationSubring']
  exact Valuation.mem_valuationSubring_iff _ _

open _root_.AlgebraicCurve.Place
private theorem _root_.AlgebraicCurve.Place.adicValuation_isRankOneDiscrete' :
  v.adicValuation.IsRankOneDiscrete :=
  IsDiscreteValuationRing.isRankOneDiscrete v.toValuationSubring F

open _root_.AlgebraicCurve.Place
private theorem _root_.AlgebraicCurve.Place.adicValuation_isTrivialOn' :
  v.adicValuation.IsTrivialOn K :=
  Valuation.IsTrivialOn.of_le_one v.adicValuation fun a =>
    v.mem_iff_adicValuation_le_one'.mp (v.algebraMap_mem' a)

open _root_.AlgebraicCurve.Place
private theorem _root_.AlgebraicCurve.Place.isEquiv_adicValuation_of_valuationSubring_eq' {Γ :
  Type*}
    [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}
    (h : w.valuationSubring = v.toValuationSubring) : w.IsEquiv v.adicValuation :=
  (Valuation.isEquiv_iff_valuationSubring _ _).mpr
    (h.trans v.adicValuation_valuationSubring'.symm)

open _root_.AlgebraicCurve.Place
private theorem ord_eq_zero_iff_adicValuation_eq_one' {f : F} (hf : f ≠ 0) :
    v.ord f = 0 ↔ v.adicValuation f = 1 := by
  simp only [ord, neg_eq_zero]
  constructor
  · intro h
    have h2 := exp_log (v.adicValuation_ne_zero hf)
    rw [h, exp_zero] at h2
    exact h2.symm
  · intro h
    rw [h, log_one]

section OfHeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
  [Algebra K R] [IsScalarTower K R F]

private theorem isEquiv_adicValuation_ofHeightOneSpectrum' (w : HeightOneSpectrum R) :
    (w.valuation F).IsEquiv (ofHeightOneSpectrum (K := K) w).adicValuation :=
  (ofHeightOneSpectrum (K := K) w).isEquiv_adicValuation_of_valuationSubring_eq' rfl

end OfHeightOneSpectrum

end Place

namespace RationalFunctionField

variable (K : Type*) [Field K]

section PlaceInfty

variable [DecidableEq (RatFunc K)]

private theorem nontrivial_valueGroup_inftyValuation :
    Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass (RatFunc.inftyValuation K))) := by
  rw [Subgroup.nontrivial_iff_exists_ne_one]
  refine ⟨Units.mk0 (RatFunc.inftyValuation K RatFunc.X)
    (by rw [RatFunc.inftyValuation.X]; exact exp_ne_zero), ?_, ?_⟩
  · exact MonoidWithZeroHom.mem_valueGroup _ ⟨RatFunc.X, rfl⟩
  · rw [ne_eq, Units.ext_iff, Units.val_mk0, Units.val_one, RatFunc.inftyValuation.X]
    simp

private def placeInfty' : Place K (RatFunc K) where
  toValuationSubring := (RatFunc.inftyValuation K).valuationSubring
  algebraMap_mem' a := by
    rw [Valuation.mem_valuationSubring_iff]
    exact Valuation.IsTrivialOn.valuation_algebraMap_le_one (v := RatFunc.inftyValuation K) a
  ne_top' := by
    have := nontrivial_valueGroup_inftyValuation K
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  isPrincipalIdealRing' :=
    haveI := nontrivial_valueGroup_inftyValuation K
    (Valuation.valuationSubring_isDiscreteValuationRing
      (RatFunc.inftyValuation K)).toIsPrincipalIdealRing

private theorem placeInfty'_ne_ofHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    placeInfty' K ≠ Place.ofHeightOneSpectrum w := by
  intro h
  refine RatFunc.adicValuation_not_isEquiv_infty_valuation w
    ((Valuation.isEquiv_iff_valuationSubring _ _).mpr ?_)
  have h2 := congrArg Place.toValuationSubring h
  rw [Place.ofHeightOneSpectrum_toValuationSubring] at h2
  exact h2.symm

end PlaceInfty

variable {K}

private theorem eq_ofHeightOneSpectrum_or_eq_placeInfty' [DecidableEq (RatFunc K)]
    (v : Place K (RatFunc K)) :
    (∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w) ∨ v = placeInfty' K := by
  have := v.adicValuation_isRankOneDiscrete'
  have := v.adicValuation_isTrivialOn'
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)).or with h | h
  · exact Or.inr (Place.ext (v.adicValuation_valuationSubring'.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp h)))
  · obtain ⟨w, hw, -⟩ := h
    exact Or.inl ⟨w, Place.ext (v.adicValuation_valuationSubring'.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp hw))⟩

theorem rowMain :
    {v : Place K (RatFunc K) |
      ∀ w : HeightOneSpectrum K[X], v ≠ Place.ofHeightOneSpectrum w}.Subsingleton := by
  classical
  intro v hv v' hv'
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty' v with ⟨w, h⟩ | h
  · exact absurd h (hv w)
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty' v' with ⟨w, h'⟩ | h'
  · exact absurd h' (hv' w)
  rw [h, h']

end RationalFunctionField

end AlgebraicCurve

end

open _root_.AlgebraicCurve in
with_weak_namespace _root_.AlgebraicCurves.Places.Rational.Proofs
open
  RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum.AlgebraicCurve
in
with_weak_namespace RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum
theorem
  _root_.AlgebraicCurve.RationalFunctionField.subsingleton_setOf_forall_ne_ofHeightOneSpectrum
  {K : Type*} [Field K] :
    {v : Place K (RatFunc K) | ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      v ≠ Place.ofHeightOneSpectrum w}.Subsingleton :=
  AlgebraicCurve.RationalFunctionField.rowMain
end RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum
end AlgebraicCurves.Places.Rational.Proofs
end ProofImplementation
