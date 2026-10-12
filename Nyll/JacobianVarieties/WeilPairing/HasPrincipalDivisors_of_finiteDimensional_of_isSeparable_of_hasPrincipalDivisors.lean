/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.JacobianVarieties.WeilPairing.Divisorial
import Nyll.AlgebraicCurves.Places.Evaluation
import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Places.OverDVR
import Nyll.AlgebraicCurves.Places.Place_ord_norm_eq_sum_fiberOver_of_isSeparable
import Nyll.AlgebraicCurves.Places.Place_mem_iff_ord_nonneg
import Nyll.AlgebraicCurves.Places.Place_ord_nonneg_of_mem

/-!
# Principal divisors in finite separable extensions

Bound the support of valuations by the coefficients of minimal polynomials.
The resulting divisor pushes forward to the norm divisor, so its degree is zero.
-/

section ProofImplementation

namespace JacobianVarieties.WeilPairing.Proofs.FiniteSeparablePrincipal

open _root_.AlgebraicCurve

noncomputable section

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace HPDSepExt
open _root_.AlgebraicCurve

open Polynomial
variable {K F L : Type*} [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L]
  [Algebra F L] [IsScalarTower K F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L] [HasPrincipalDivisors K F]

open Classical in
/-- The finite support of a principal divisor of a nonzero coefficient. -/
def badOf (c : F) : Finset (Place K F) :=
  if hc : c = 0 then ∅ else (HasPrincipalDivisors.exists_divisor (K := K) c hc).choose.support

theorem ord_eq_zero_of_not_mem_badOf {c : F} {v : Place K F} (hv : v ∉ badOf (K := K) c)
    (hc : c ≠ 0) : v.ord c = 0 := by
  classical
  unfold badOf at hv
  rw [dite_eq_right hc] at hv
  have hD := (HasPrincipalDivisors.exists_divisor (K := K) c hc).choose_spec.1 v
  rw [← hD]
  by_contra h
  exact hv (Finsupp.mem_support_iff.mpr h)

open Classical in
/-- Places at which some coefficient of a polynomial may have nonzero order. -/
def badPoly (P : Polynomial F) : Finset (Place K F) :=
  P.support.biUnion fun i => badOf (K := K) (P.coeff i)

theorem coeff_mem_of_not_mem_badPoly {P : Polynomial F} {v : Place K F}
    (hv : v ∉ badPoly (K := K) P) (i : ℕ) :
    P.coeff i ∈ v.toValuationSubring := by
  classical
  by_cases hci : P.coeff i = 0
  · rw [hci]; exact zero_mem _
  have hi : i ∈ P.support := Polynomial.mem_support_iff.mpr hci
  have hv' : v ∉ badOf (K := K) (P.coeff i) := by
    intro h; apply hv; unfold badPoly; exact Finset.mem_biUnion.mpr ⟨i, hi, h⟩
  exact (Place.mem_iff_ord_nonneg v hci).mpr (le_of_eq (ord_eq_zero_of_not_mem_badOf hv' hci).symm)

omit [FiniteDimensional F L] in
theorem mem_of_aeval_eq_zero {P : Polynomial F} (hP : P.Monic) {x : L} (hx : aeval x P = 0)
    (w : Place K L)
    (hw : w.restrict F ∉ badPoly (K := K) P) : x ∈ w.toValuationSubring := by
  refine Place.mem_of_eval_monic_eq_zero w (P := P.map (algebraMap F L)) (hP.map _) (fun i => ?_) ?_
  · rw [coeff_map]
    exact (Place.mem_restrict_iff w).mp (coeff_mem_of_not_mem_badPoly hw i)
  · rwa [eval_map, ← aeval_def]

open Classical in
/-- Exceptional places from the minimal polynomials of an element and its inverse. -/
def bad (g : L) :
    Finset (Place K F) := badPoly (K := K) (minpoly F g) ∪ badPoly (K := K) (minpoly F g⁻¹)

theorem ord_eq_zero_of_restrict_not_mem_bad {g : L} (_hg : g ≠ 0) (w : Place K L)
    (hw : w.restrict F ∉ bad (K := K) (F := F) g) :
    w.ord g = 0 := by
  classical
  have hint : IsIntegral F g := IsIntegral.of_finite F g
  have hint' : IsIntegral F g⁻¹ := IsIntegral.of_finite F g⁻¹
  have h1 : g ∈ w.toValuationSubring :=
    mem_of_aeval_eq_zero (minpoly.monic hint) (minpoly.aeval F g) w
      (fun h => hw (Finset.mem_union_left _ h))
  have h2 : g⁻¹ ∈ w.toValuationSubring :=
    mem_of_aeval_eq_zero (minpoly.monic hint') (minpoly.aeval F g⁻¹) w
      (fun h => hw (Finset.mem_union_right _ h))
  have e1 := Place.ord_nonneg_of_mem w h1
  have e2 := Place.ord_nonneg_of_mem w h2
  rw [Place.ord_inv] at e2
  omega

open Classical in
/-- Places above the finite exceptional set of the element and its inverse. -/
def suppOf (g : L) : Finset (Place K L) := (bad (K := K) (F := F) g).biUnion fun v => v.fiberOver L

theorem mem_suppOf_of_ord_ne_zero {g : L} (hg : g ≠ 0) {w : Place K L} (hw : w.ord g ≠ 0) :
    w ∈ suppOf (K := K) (F := F) g := by
  classical
  by_contra h
  apply hw
  apply ord_eq_zero_of_restrict_not_mem_bad (F := F) hg
  intro hb
  apply h
  unfold suppOf
  exact Finset.mem_biUnion.mpr ⟨_, hb, Place.restrict_mem_fiberOver w⟩

open Classical in
/-- The divisor with coefficients given by the orders of a nonzero element. -/
def divOf {g : L} (hg : g ≠ 0) : Divisor K L :=
  Finsupp.onFinset (suppOf (K := K) (F := F) g) (fun w => w.ord g)
    (fun _w hw => mem_suppOf_of_ord_ne_zero (F := F) hg hw)

@[scoped simp] theorem divOf_apply {g : L} (hg : g ≠ 0) (w : Place K L) :
    divOf (K := K) (F := F) hg w = w.ord g := by
  exact Finsupp.onFinset_apply

theorem pushforward_divOf_apply {g : L} (hg : g ≠ 0) (v : Place K F) :
    Divisor.pushforward F (divOf (K := K) (F := F) hg) v = v.ord (Algebra.norm F g) := by
  classical
  rw [Divisor.pushforward_apply, Place.ord_norm_eq_sum_fiberOver_of_isSeparable v hg]
  rw [← Finset.sum_filter]
  have hsub : (divOf (K := K) (F := F) hg).support.filter (fun w => w.restrict F = v)
      ⊆ v.fiberOver L := by
    intro w hw
    rw [Finset.mem_filter] at hw
    exact (Place.mem_fiberOver v).mpr hw.2
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [divOf_apply, mul_comm]
  · intro w hwf hwn
    have hres : w.restrict F = v := (Place.mem_fiberOver v).mp hwf
    have : w ∉ (divOf (K := K) (F := F) hg).support :=
      fun h => hwn (Finset.mem_filter.mpr ⟨h, hres⟩)
    rw [Finsupp.mem_support_iff, not_not, divOf_apply] at this
    rw [this, mul_zero]

theorem degree_divOf {g : L} (hg : g ≠ 0) : Divisor.degree (divOf (K := K) (F := F) hg) = 0 := by
  obtain ⟨E, hE, hdeg⟩ := HasPrincipalDivisors.exists_divisor
    (K := K) (Algebra.norm F g) (Algebra.norm_ne_zero_iff.mpr hg)
  have hpush : Divisor.pushforward F (divOf (K := K) (F := F) hg) = E := by
    ext v; rw [pushforward_divOf_apply, hE]
  rw [← Divisor.degree_pushforward (F := F), hpush, hdeg]

end AlgebraicCurve.HPDSepExt

end

open AlgebraicCurve.HPDSepExt in
with_weak_namespace _root_.AlgebraicCurve
theorem hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors
    (K F L : Type*) [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L]
    [Algebra F L] [IsScalarTower K F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L] [HasPrincipalDivisors K F] :
    HasPrincipalDivisors K L  :=
  ⟨fun _g hg => ⟨divOf (K := K) (F := F) hg, fun w => divOf_apply hg w, degree_divOf hg⟩⟩
end JacobianVarieties.WeilPairing.Proofs.FiniteSeparablePrincipal
end ProofImplementation

attribute [-instance]
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance]
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp]
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
