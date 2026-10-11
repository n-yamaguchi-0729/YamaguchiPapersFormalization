/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.OverDVR
import Nyll.AlgebraicCurves.Divisors.Semilinear
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Invariant.Basic
import Nyll.AlgebraicCurves.Divisors.Maps
import Mathlib.FieldTheory.Galois.Basic

/-!
# Place exists alg Equiv smul eq of restrict eq
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_exists_algEquiv_smul_eq_of_restrict_eq

noncomputable section
open _root_.AlgebraicCurve
open _root_.IsDedekindDomain
open scoped Pointwise

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

variable {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
  [Algebra F' M] [IsScalarTower K F' M]

section Restrict
variable [Algebra.IsIntegral F' M]

private theorem restrict_ofAlgAut_restrictScalars_smul (σ : M ≃ₐ[F'] M) (W : Place K M) :
    (SemilinearAut.ofAlgAut (σ.restrictScalars K) • W).restrict F' = W.restrict F' := by
  refine Place.ext ?_
  ext x
  rw [restrict_toValuationSubring, restrict_toValuationSubring, ValuationSubring.mem_comap,
    ValuationSubring.mem_comap, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, SemilinearAut.inv_smul_def,
    SemilinearAut.toRingAut_ofAlgAut]
  have : ((σ.restrictScalars K : M ≃+* M).symm (algebraMap F' M x)) = algebraMap F' M x := by
    rw [RingEquiv.symm_apply_eq]
    exact (σ.commutes x).symm
  rw [this]

private theorem ord_smul_eq (g : SemilinearAut K M) (W : Place K M) (y : M) :
    (g • W).ord y = W.ord (g⁻¹ • y) := by
  conv_lhs => rw [← smul_inv_smul g y]
  exact SemilinearAut.ord_smul g W (g⁻¹ • y)

end Restrict

end Place
end AlgebraicCurve

open _root_.AlgebraicCurve.Place AlgebraicCurve.Place in
theorem _root_.AlgebraicCurve.Place.exists_algEquiv_smul_eq_of_restrict_eq {K F' M : Type*} [Field
  K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [IsGalois F' M] (W W' : Place K M)
    (h : W'.restrict F' = W.restrict F') :
    ∃ σ : M ≃ₐ[F'] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W = W' := by
  set w : Place K F' := W.restrict F'
  have hW : W.restrict F' = w := rfl
  let := IsIntegralClosure.MulSemiringAction w.toValuationSubring F' M (integralClosureAt M w)
  have : IsGaloisGroup Gal(M/F') w.toValuationSubring (integralClosureAt M w) :=
    IsGaloisGroup.of_isFractionRing Gal(M/F') w.toValuationSubring (integralClosureAt M w) F' M
  have hp : (fiberCenter M w hW).asIdeal.IsPrime := (fiberCenter M w hW).isPrime
  have hp' : (fiberCenter M w h).asIdeal.IsPrime := (fiberCenter M w h).isPrime
  have := fiberCenter_liesOver (F' := M) hW
  have := fiberCenter_liesOver (F' := M) h
  obtain ⟨σ, hσ'⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    (IsLocalRing.maximalIdeal w.toValuationSubring) (fiberCenter M w hW).asIdeal
    (fiberCenter M w h).asIdeal Gal(M/F')
  refine ⟨σ, eq_of_fiberCenter_eq (restrict_ofAlgAut_restrictScalars_smul σ W) h ?_⟩
  refine HeightOneSpectrum.ext (Ideal.ext fun c => ?_)
  rw [← hσ', Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  by_cases hc : c = 0
  · simp [hc]
  have hc' : σ⁻¹ • c ≠ 0 := fun h0 => hc (by simpa using congrArg (σ • ·) h0)
  rw [mem_fiberCenter_iff_ord_pos _ hc, mem_fiberCenter_iff_ord_pos _ hc', ord_smul_eq,
    SemilinearAut.inv_smul_def, SemilinearAut.toRingAut_ofAlgAut]
  have key : algebraMap (integralClosureAt M w) M (σ⁻¹ • c)
      = ((σ.restrictScalars K : M ≃+* M)).symm (algebraMap (integralClosureAt M w) M c) := by
    rw [show σ⁻¹ • c = galRestrict w.toValuationSubring F' M (integralClosureAt M w) σ⁻¹ c
      from rfl, algebraMap_galRestrict_apply, AlgEquiv.aut_inv]
    rfl
  rw [key]

end
end AlgebraicCurves.Places.Proofs.Place_exists_algEquiv_smul_eq_of_restrict_eq
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
