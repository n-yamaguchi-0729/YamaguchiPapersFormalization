/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_add_of_adjoin_eq_top.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Places.OverDVR
import AlgebraicCurves.Places.Place_sum_ramificationIndex_mul_inertiaDeg_exchange_add

/-!
# Divisor pullback Along pushforward Along eq add of adjoin eq top
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs
namespace Divisor_pullbackAlong_pushforwardAlong_eq_add_of_adjoin_eq_top

open AlgebraicCurve

namespace X2Glue

theorem algebra_adjoin_eq_top_of_intermediateField {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E] [FiniteDimensional F E]
    {S : Set E} (hS : IntermediateField.adjoin K S = ⊤) : Algebra.adjoin F S = ⊤ := by
  have hS' : IntermediateField.adjoin F S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ IntermediateField.adjoin K S := hS ▸ IntermediateField.mem_top
    have hle : IntermediateField.adjoin K S ≤ (IntermediateField.adjoin F S).restrictScalars K :=
      IntermediateField.adjoin_le_iff.mpr fun y hy => IntermediateField.subset_adjoin F S hy
    exact hle hx
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun x _ => Algebra.IsAlgebraic.isAlgebraic x), hS', IntermediateField.top_toSubalgebra]

end X2Glue

theorem _root_.AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_add_of_adjoin_eq_top
    {K F F₁ F₂ Z Z' : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field Z] [Field Z']
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z] [Algebra K Z'] [CharZero K]
    [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K Z] [HasPrincipalDivisors K Z']
    (φ : F →ₐ[K] F₁) (ψ' : F →ₐ[K] F₂)
    (u : F₁ →ₐ[K] Z) (u' : F₂ →ₐ[K] Z) (s : F₁ →ₐ[K] Z') (s' : F₂ →ₐ[K] Z')
    (hsq : u.comp φ = u'.comp ψ') (hsq' : s.comp φ = s'.comp ψ')
    (hφ : φ.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral)
    (hu : u.toRingHom.IsIntegral) (hu' : u'.toRingHom.IsIntegral)
    (hs : s.toRingHom.IsIntegral) (hs' : s'.toRingHom.IsIntegral)
    (hφfin : FiniteAlong K φ) (hψ'fin : FiniteAlong K ψ')
    (hufin : FiniteAlong K u) (hu'fin : FiniteAlong K u')
    (hsfin : FiniteAlong K s) (hs'fin : FiniteAlong K s')
    (hgen : IntermediateField.adjoin K (Set.range u ∪ Set.range u') = ⊤)
    (hgen' : IntermediateField.adjoin K (Set.range s ∪ Set.range s') = ⊤)
    (hdeg : finrankAlong K u' + finrankAlong K s' = finrankAlong K φ)
    (hne : ∃ (a : F₁) (b : F₂), s a = s' b ∧ u a ≠ u' b)
    (D : Divisor K F₂) :
    Divisor.pullbackAlong φ hφ (Divisor.pushforwardAlong ψ' hψ' D)
      = Divisor.pushforwardAlong u hu (Divisor.pullbackAlong u' hu' D)
        + Divisor.pushforwardAlong s hs (Divisor.pullbackAlong s' hs' D) := by
  classical
  let : Algebra F F₁ := algebraAlong φ
  let : Algebra F F₂ := algebraAlong ψ'
  let : Algebra F₁ Z := algebraAlong u
  let : Algebra F₂ Z := algebraAlong u'
  let : Algebra F₁ Z' := algebraAlong s
  let : Algebra F₂ Z' := algebraAlong s'
  let : Algebra F Z := algebraAlong (u.comp φ)
  let : Algebra F Z' := algebraAlong (s.comp φ)
  have : IsScalarTower K F F₁ := isScalarTower_along φ
  have : IsScalarTower K F F₂ := isScalarTower_along ψ'
  have : IsScalarTower K F₁ Z := isScalarTower_along u
  have : IsScalarTower K F₂ Z := isScalarTower_along u'
  have : IsScalarTower K F₁ Z' := isScalarTower_along s
  have : IsScalarTower K F₂ Z' := isScalarTower_along s'
  have : IsScalarTower K F Z := isScalarTower_along (u.comp φ)
  have : IsScalarTower K F Z' := isScalarTower_along (s.comp φ)
  have : IsScalarTower F F₁ Z := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower F F₂ Z := IsScalarTower.of_algebraMap_eq fun x => AlgHom.congr_fun hsq x
  have : IsScalarTower F F₁ Z' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower F F₂ Z' := IsScalarTower.of_algebraMap_eq fun x => AlgHom.congr_fun hsq' x
  have : Algebra.IsIntegral F F₁ := isIntegral_along φ hφ
  have : Algebra.IsIntegral F F₂ := isIntegral_along ψ' hψ'
  have : Algebra.IsIntegral F₁ Z := isIntegral_along u hu
  have : Algebra.IsIntegral F₂ Z := isIntegral_along u' hu'
  have : Algebra.IsIntegral F₁ Z' := isIntegral_along s hs
  have : Algebra.IsIntegral F₂ Z' := isIntegral_along s' hs'
  have : FiniteDimensional F F₁ := hφfin
  have : FiniteDimensional F F₂ := hψ'fin
  have : FiniteDimensional F₁ Z := hufin
  have : FiniteDimensional F₂ Z := hu'fin
  have : FiniteDimensional F₁ Z' := hsfin
  have : FiniteDimensional F₂ Z' := hs'fin
  have : FiniteDimensional F Z := Module.Finite.trans F₁ Z
  have : FiniteDimensional F Z' := Module.Finite.trans F₁ Z'
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have hgenZ : Algebra.adjoin F (Set.range (algebraMap F₂ Z) ∪ Set.range (algebraMap F₁ Z)) = ⊤ :=
    by
    rw [Set.union_comm]; exact X2Glue.algebra_adjoin_eq_top_of_intermediateField (K := K) hgen
  have hgenZ' : Algebra.adjoin F (Set.range (algebraMap F₂ Z') ∪ Set.range (algebraMap F₁ Z')) = ⊤
    := by
    rw [Set.union_comm]; exact X2Glue.algebra_adjoin_eq_top_of_intermediateField (K := K) hgen'
  have hdeg' : Module.finrank F₂ Z + Module.finrank F₂ Z' = Module.finrank F F₁ := hdeg
  have hne' : ∃ (a : F₁) (b : F₂), algebraMap F₁ Z' a = algebraMap F₂ Z' b ∧
      algebraMap F₁ Z a ≠ algebraMap F₂ Z b := hne
  have eZ : ∀ W : Place K Z, Place.ramificationIndexAlong u' W = W.ramificationIndex F₂ := fun _ =>
    rfl
  have fZ : ∀ W : Place K Z, W.inertiaDegAlong u hu = W.inertiaDeg F₁ := fun _ => rfl
  have eZ' : ∀ W : Place K Z', Place.ramificationIndexAlong s' W = W.ramificationIndex F₂ := fun _
    => rfl
  have fZ' : ∀ W : Place K Z', W.inertiaDegAlong s hs = W.inertiaDeg F₁ := fun _ => rfl
  have fF : ∀ w : Place K F₂, w.inertiaDegAlong ψ' hψ' = w.inertiaDeg F := fun _ => rfl
  have eF : ∀ w : Place K F₁, Place.ramificationIndexAlong φ w = w.ramificationIndex F := fun _ =>
    rfl
  have hrr : ∀ W : Place K Z, (W.restrict F₁).restrict F = (W.restrict F₂).restrict F := fun W =>
    Place.ext (by simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])
  have hrr' : ∀ W : Place K Z', (W.restrict F₁).restrict F = (W.restrict F₂).restrict F := fun W =>
    Place.ext (by simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])
  suffices h : (Divisor.pullbackAlong φ hφ).comp (Divisor.pushforwardAlong ψ' hψ') =
      (Divisor.pushforwardAlong u hu).comp (Divisor.pullbackAlong u' hu')
        + (Divisor.pushforwardAlong s hs).comp (Divisor.pullbackAlong s' hs') from
    DFunLike.congr_fun h D
  refine Finsupp.addHom_ext fun wA n => ?_
  simp only [AddMonoidHom.coe_comp, AddMonoidHom.add_apply, Function.comp_apply]
  rw [Divisor.pushforwardAlong_single, Divisor.pullbackAlong_single, Divisor.pullbackAlong_single,
    Divisor.pullbackAlong_single, map_sum, map_sum]
  simp only [Divisor.pushforwardAlong_single]
  ext wB
  rw [Finsupp.add_apply, Finset.sum_apply', Finset.sum_apply', Finset.sum_apply']
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', eZ, fZ, eZ', fZ', fF, eF]
  by_cases hv : wB.restrictAlong φ hφ = wA.restrictAlong ψ' hψ'
  · rw [ite_eq_left (Place.mem_fiberAlong.mpr hv), ← Finset.sum_filter, ← Finset.sum_filter]
    have hT : ∀ W, W ∈ (Place.fiberAlong u' hu' wA).filter (fun W => W.restrictAlong u hu = wB)
        ↔ W.restrict F₂ = wA ∧ W.restrict F₁ = wB := fun W => by
      rw [Finset.mem_filter, Place.mem_fiberAlong]
      exact Iff.rfl
    have hT' : ∀ W, W ∈ (Place.fiberAlong s' hs' wA).filter (fun W => W.restrictAlong s hs = wB)
        ↔ W.restrict F₂ = wA ∧ W.restrict F₁ = wB := fun W => by
      rw [Finset.mem_filter, Place.mem_fiberAlong]
      exact Iff.rfl
    have key := AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange_add
      (K := K) (F := F) (F₁ := F₂) (F₂ := F₁) (Z := Z) (Z' := Z')
      hgenZ hgenZ' hdeg' hne' wA wB (Eq.symm hv) _ hT _ hT'
    rw [Finset.sum_congr rfl fun W _ => mul_assoc n _ _,
      Finset.sum_congr rfl fun W _ => mul_assoc n _ _, ← Finset.mul_sum, ← Finset.mul_sum,
      ← mul_add, mul_assoc]
    congr 1
    exact_mod_cast key.symm
  · rw [ite_eq_right (fun h => hv (Place.mem_fiberAlong.mp h))]
    have h0 : ∑ W ∈ Place.fiberAlong u' hu' wA,
        (if Place.restrictAlong u hu W = wB then n * (W.ramificationIndex F₂ : ℤ) * (W.inertiaDeg
          F₁ : ℤ)
          else 0) = 0 := by
      refine Finset.sum_eq_zero fun W hW => ?_
      rw [ite_eq_right]
      intro hWB
      apply hv
      have h₁ : W.restrict F₂ = wA := Place.mem_fiberAlong.mp hW
      have h₂ : W.restrict F₁ = wB := hWB
      change wB.restrict F = wA.restrict F
      rw [← h₁, ← h₂, hrr]
    have h0' : ∑ W ∈ Place.fiberAlong s' hs' wA,
        (if Place.restrictAlong s hs W = wB then n * (W.ramificationIndex F₂ : ℤ) * (W.inertiaDeg
          F₁ : ℤ)
          else 0) = 0 := by
      refine Finset.sum_eq_zero fun W hW => ?_
      rw [ite_eq_right]
      intro hWB
      apply hv
      have h₁ : W.restrict F₂ = wA := Place.mem_fiberAlong.mp hW
      have h₂ : W.restrict F₁ = wB := hWB
      change wB.restrict F = wA.restrict F
      rw [← h₁, ← h₂, hrr']
    rw [h0, h0', add_zero]
end AlgebraicCurves.Divisors.Proofs.Divisor_pullbackAlong_pushforwardAlong_eq_add_of_adjoin_eq_top
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
