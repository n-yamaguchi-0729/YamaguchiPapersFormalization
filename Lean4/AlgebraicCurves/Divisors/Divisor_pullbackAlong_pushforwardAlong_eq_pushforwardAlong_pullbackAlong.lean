/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Correspondences
import Mathlib.FieldTheory.Separable
import AlgebraicCurves.Places.Place_sum_ramificationIndex_mul_inertiaDeg_exchange

/-!
# Divisor pullback Along pushforward Along eq pushforward Along pullback Along
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs
namespace Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
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

open AlgebraicCurve

namespace BifibreWEX

theorem restrict_restrict {K F E M : Type*} [Field K] [Field F] [Field E] [Field M]
    [Algebra K F] [Algebra K E] [Algebra K M] [Algebra F E] [Algebra E M] [Algebra F M]
    [IsScalarTower F E M] [IsScalarTower K F E] [IsScalarTower K E M] [IsScalarTower K F M]
    [Algebra.IsIntegral F E] [Algebra.IsIntegral E M] [Algebra.IsIntegral F M] (W : Place K M) :
    (W.restrict E).restrict F = W.restrict F :=
  Place.ext (by
    simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])

end BifibreWEX

theorem
  _root_.AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
    {K F A B E : Type*} [Field K] [Field F] [Field A] [Field B] [Field E]
    [Algebra K F] [Algebra K A] [Algebra K B] [Algebra K E]
    [HasPrincipalDivisors K B] [HasPrincipalDivisors K E]
    (a : F →ₐ[K] A) (b : F →ₐ[K] B) (a' : A →ₐ[K] E) (b' : B →ₐ[K] E)
    (ha : a.toRingHom.IsIntegral) (hb : b.toRingHom.IsIntegral)
    (ha' : a'.toRingHom.IsIntegral) (hb' : b'.toRingHom.IsIntegral)
    (hsq : b'.comp b = a'.comp a)
    (hfin : FiniteAlong K (a'.comp a)) (hsep : SeparableAlong K (a'.comp a))
    (hgen : Algebra.adjoin K (Set.range a' ∪ Set.range b') = ⊤)
    (hLD : finrankAlong K (a'.comp a) = finrankAlong K a * finrankAlong K b)
    (D : Divisor K A) :
    Divisor.pullbackAlong b hb (Divisor.pushforwardAlong a ha D) =
      Divisor.pushforwardAlong b' hb' (Divisor.pullbackAlong a' ha' D) := by
  classical
  let : Algebra F A := algebraAlong a
  let : Algebra F B := algebraAlong b
  let : Algebra A E := algebraAlong a'
  let : Algebra B E := algebraAlong b'
  let : Algebra F E := algebraAlong (a'.comp a)
  have : IsScalarTower K F A := isScalarTower_along a
  have : IsScalarTower K F B := isScalarTower_along b
  have : IsScalarTower K A E := isScalarTower_along a'
  have : IsScalarTower K B E := isScalarTower_along b'
  have : IsScalarTower K F E := isScalarTower_along (a'.comp a)
  have : IsScalarTower F A E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower F B E :=
    IsScalarTower.of_algebraMap_eq fun x => (AlgHom.congr_fun hsq x).symm
  have : Algebra.IsIntegral F A := isIntegral_along a ha
  have : Algebra.IsIntegral F B := isIntegral_along b hb
  have : Algebra.IsIntegral A E := isIntegral_along a' ha'
  have : Algebra.IsIntegral B E := isIntegral_along b' hb'
  have : Module.Finite F E := hfin
  have : Algebra.IsIntegral F E := Algebra.IsIntegral.of_finite F E
  have : Algebra.IsSeparable F E := hsep
  have : FiniteDimensional A E := Module.Finite.of_restrictScalars_finite F A E
  have : FiniteDimensional B E := Module.Finite.of_restrictScalars_finite F B E
  have : FiniteDimensional F A := Module.Finite.left F A E
  have : FiniteDimensional F B := Module.Finite.left F B E
  have hgenF : Algebra.adjoin F (Set.range (algebraMap A E) ∪ Set.range (algebraMap B E)) = ⊤ := by
    have hs : Set.range (algebraMap A E) ∪ Set.range (algebraMap B E) =
        Set.range a' ∪ Set.range b' := rfl
    rw [hs, eq_top_iff]
    intro z _
    have hz : z ∈ Algebra.adjoin K (Set.range a' ∪ Set.range b') := hgen ▸ Algebra.mem_top
    have hle : Algebra.adjoin K (Set.range a' ∪ Set.range b') ≤
        (Algebra.adjoin F (Set.range a' ∪ Set.range b')).restrictScalars K :=
      Algebra.adjoin_le fun x hx =>
        (Subalgebra.mem_restrictScalars K).mpr (Algebra.subset_adjoin hx)
    exact (Subalgebra.mem_restrictScalars K).mp (hle hz)
  have eA : ∀ W : Place K E, Place.ramificationIndexAlong a' W = W.ramificationIndex A :=
    fun _ => rfl
  have fB : ∀ W : Place K E, W.inertiaDegAlong b' hb' = W.inertiaDeg B := fun _ => rfl
  have fF : ∀ w : Place K A, w.inertiaDegAlong a ha = w.inertiaDeg F := fun _ => rfl
  have eF : ∀ w : Place K B, Place.ramificationIndexAlong b w = w.ramificationIndex F :=
    fun _ => rfl
  suffices h : (Divisor.pullbackAlong b hb).comp (Divisor.pushforwardAlong a ha) =
      (Divisor.pushforwardAlong b' hb').comp (Divisor.pullbackAlong a' ha') from
    DFunLike.congr_fun h D
  refine Finsupp.addHom_ext fun wA n => ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply]
  rw [Divisor.pushforwardAlong_single, Divisor.pullbackAlong_single, Divisor.pullbackAlong_single,
    map_sum]
  simp only [Divisor.pushforwardAlong_single]
  ext wB
  rw [Finset.sum_apply', Finset.sum_apply']
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', eA, fB, fF, eF]
  by_cases hv : wB.restrictAlong b hb = wA.restrictAlong a ha
  · rw [ite_eq_left (Place.mem_fiberAlong.mpr hv), ← Finset.sum_filter]
    have hT : ∀ W, W ∈ (Place.fiberAlong a' ha' wA).filter (fun W => W.restrictAlong b' hb' = wB)
        ↔ W.restrict A = wA ∧ W.restrict B = wB := fun W => by
      rw [Finset.mem_filter, Place.mem_fiberAlong]
      exact Iff.rfl
    have key := AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange
      (K := K) (F := F) (F₁ := A) (F₂ := B) (E := E) hgenF hLD (wA.restrictAlong a ha) wA wB
      rfl hv _ hT
    rw [Finset.sum_congr rfl fun W _ => mul_assoc n _ _, ← Finset.mul_sum, mul_assoc]
    congr 1
    exact_mod_cast key.symm
  · rw [ite_eq_right (fun h => hv (Place.mem_fiberAlong.mp h))]
    symm
    refine Finset.sum_eq_zero fun W hW => ?_
    rw [ite_eq_right]
    intro hWB
    apply hv
    have h₁ : W.restrict A = wA := Place.mem_fiberAlong.mp hW
    have h₂ : W.restrict B = wB := hWB
    change wB.restrict F = wA.restrict F
    rw [← h₁, ← h₂, BifibreWEX.restrict_restrict, BifibreWEX.restrict_restrict]
end Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
end AlgebraicCurves.Divisors.Proofs
end ProofImplementation
