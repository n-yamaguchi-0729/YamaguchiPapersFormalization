/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Dimension drop for a principal quotient of a local Noetherian ring

An element in the maximal ideal that avoids every minimal prime lowers the dimension by one.
The same element and the actual quotient by its principal ideal are used throughout.
-/

@[expose] public section

universe u

open RingTheory
open scoped Pointwise

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The self-module quotient by an element avoiding all minimal primes drops dimension by one. -/
theorem ringKrullDim_quotSMulTop_add_one_of_forall_minimalPrimes_notMem
    {x : R} (hx : x ∈ maximalIdeal R) (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ringKrullDim (QuotSMulTop x R) + 1 = ringKrullDim R := by
  rw [← Module.supportDim_quotient_eq_ringKrullDim, ← Module.supportDim_self_eq_ringKrullDim]
  refine Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    ?_ hx
  intro p hp
  refine hxmin p ?_
  rwa [Module.annihilator_eq_bot.mpr (inferInstance : FaithfulSMul R R)] at hp

/-- The actual principal-ideal quotient has dimension one less under minimal-prime avoidance. -/
theorem ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem
    {x : R} (hx : x ∈ maximalIdeal R) (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by
  have hkey : ringKrullDim (QuotSMulTop x R) + 1 = ringKrullDim R :=
    ringKrullDim_quotSMulTop_add_one_of_forall_minimalPrimes_notMem hx hxmin
  have hspan : Ideal.span {x} = x • (⊤ : Ideal R) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq R hspan).toRingEquiv]
  exact hkey

end IsLocalRing
