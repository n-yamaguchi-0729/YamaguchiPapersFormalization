/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteIdealCanonicalTameCharacter
import EtaleFundamentalGroups.Inertia.FiniteIdealTameRamification
import EtaleFundamentalGroups.Inertia.FiniteIdealTameFactorization
import EtaleFundamentalGroups.Inertia.FiniteIdealWildPrimary
import ValuedFieldTheory.Ramification.HilbertRamification.TameNormalizationExponent
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.Algebra.CharP.Defs

/-!
# Characteristic powers in tame normalization

Derives that the finite normalization exponent is a power of the residue exponential
characteristic using wild-order and inertia-cardinality formulas.
-/

namespace EtaleFundamentalGroups.Inertia

open RamificationTheory.HilbertRamification

universe u v

/-- The actual e/n exponent is a power of the actual residue exponential
characteristic, derived from the same principal-unit wild group and both
original inertia-cardinality formulas. No power assertion is an input. -/
theorem finiteIdealNormalizationExponent_exists_expChar_pow
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [IsGaloisGroup (B ≃ₐ[A] B) A B]
    (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver (IsLocalRing.maximalIdeal A)] (hQ : Q ≠ ⊥) :
    ∃ a : ℕ, finiteIdealNormalizationExponent A B (B ≃ₐ[A] B) Q hQ =
      (ringExpChar Q.ResidueField) ^ a := by
  have hn := finiteIdealTameOrder_pos B (B ≃ₐ[A] B) Q hQ
  have hne := finiteIdealTameOrder_dvd_ramificationIdx A B (B ≃ₐ[A] B) Q hQ
  obtain ⟨f, hcard⟩ :=
    finiteIdealTameOrder_mul_wildOrder_eq_ramificationIdx_mul A B Q hQ (B ≃ₐ[A] B)
  obtain ⟨a, hw⟩ := finiteIdealWildOrder_exists_expChar_pow A B Q hQ
  rcases expChar_is_prime_or_one Q.ResidueField (ringExpChar Q.ResidueField) with hp | hp
  · exact tameNormalizationExponent_eq_prime_pow hp hn hne hcard hw
  · refine ⟨0, ?_⟩
    rw [pow_zero]
    have hwone : finiteIdealWildOrder B (B ≃ₐ[A] B) Q hQ = 1 := by
      simpa only [hp, one_pow] using hw
    exact tameNormalizationExponent_eq_one_of_wild_eq_one hn hne hcard hwone

end EtaleFundamentalGroups.Inertia
