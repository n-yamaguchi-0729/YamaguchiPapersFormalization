/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Places.Place_sum_ramificationIndex_mul_inertiaDeg
import AlgebraicCurves.Places.Place_inertiaDeg_pos

/-!
# Place ramification Index Along eq of pow eq of is Coprime ord
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord
    {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
      [AlgebraicCurve.HasPrincipalDivisors k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : AlgebraicCurve.FiniteAlong k φ) (hsep : AlgebraicCurve.SeparableAlong k φ)
    (n : ℕ) (hdeg : AlgebraicCurve.finrankAlong k φ = n)
    (c : F') (u : F) (hu : φ u = c ^ n)
    (P : AlgebraicCurve.Place k F')
    (hcop : IsCoprime ((P.restrictAlong φ hφ).ord u) (n : ℤ)) :
    P.ramificationIndexAlong φ = n := by
  classical
  let alg : Algebra F F' := φ.toRingHom.toAlgebra
  have : IsScalarTower k F F' := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  have : Algebra.IsIntegral F F' := ⟨hφ⟩
  have : Module.Finite F F' := hfin
  have : Algebra.IsSeparable F F' := hsep
  have hdeg' : Module.finrank F F' = n := hdeg
  change P.ramificationIndex F = n
  set v : Place k F := P.restrict F with hvdef
  have hv : P.restrictAlong φ hφ = v := rfl
  rw [hv] at hcop
  set e : ℕ := P.ramificationIndex F with hedef
  have hepos : 0 < e := P.ramificationIndex_pos (F := F)
  have hord : P.ord (algebraMap F F' u) = e * v.ord u := P.ord_restrict u
  have hord' : P.ord (algebraMap F F' u) = n * P.ord c := by
    rw [show algebraMap F F' u = c ^ n from hu, ← zpow_natCast, P.ord_zpow]
  have hdvdZ : (n : ℤ) ∣ (e : ℤ) := by
    apply hcop.symm.dvd_of_dvd_mul_right
    rw [← hord, hord']
    exact dvd_mul_right _ _
  have hdvd : n ∣ e := Int.natCast_dvd_natCast.mp hdvdZ
  have hsum := AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg (K := k) (F := F) (F' :=
    F') v
  have hmem : P ∈ v.fiber F' := P.restrict_mem_fiber (F := F)
  have hfpos : 0 < P.inertiaDeg F := AlgebraicCurve.Place.inertiaDeg_pos (K := k) (F := F) P
  have hle : (e : ℤ) * (P.inertiaDeg F : ℤ) ≤ (Module.finrank F F' : ℤ) := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun w : Place k F' => (w.ramificationIndex F : ℤ) *
      (w.inertiaDeg F : ℤ))
      (fun w _ => mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)) hmem
  have hlen : e ≤ n := by
    have h1 : (e : ℤ) ≤ (e : ℤ) * (P.inertiaDeg F : ℤ) := by
      have : (1 : ℤ) ≤ (P.inertiaDeg F : ℤ) := by exact_mod_cast hfpos
      nlinarith
    have h2 : (e : ℤ) ≤ (n : ℤ) := by rw [← hdeg']; exact h1.trans hle
    exact_mod_cast h2
  obtain ⟨m, hm⟩ := hdvd
  have hn0 : 0 < n := by
    rw [← hdeg']; exact Module.finrank_pos
  have hm1 : m = 1 := by
    have hm0 : 0 < m := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hm; omega)
    have : n * m ≤ n * 1 := by rw [mul_one, ← hm]; exact hlen
    have := Nat.le_of_mul_le_mul_left this hn0
    omega
  rw [hm, hm1, mul_one]
end AlgebraicCurves.Places.Proofs.Place_ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
