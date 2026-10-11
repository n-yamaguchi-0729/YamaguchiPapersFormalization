/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteIdealNormalizationPower
import EtaleFundamentalGroups.Inertia.TameOrderDivisibility
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Coprimality of finite normalization exponents

Proves that an integer invertible in the original base ring is coprime to the finite ideal
character normalization exponent.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- Every integer invertible in the original base is coprime to the actual
normalization exponent. The residue-field calculation and the characteristic
power supplier are confined to this single finite extension. -/
theorem finiteIdealNormalizationExponent_coprime_of_isUnit_base
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [IsGaloisGroup (B ≃ₐ[A] B) A B]
    (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver (IsLocalRing.maximalIdeal A)] (hQ : Q ≠ ⊥)
    (n : ℕ) (hn : IsUnit (n : A)) :
    Nat.Coprime n (finiteIdealNormalizationExponent A B (B ≃ₐ[A] B) Q hQ) := by
  have hnQ : IsUnit (n : Q.ResidueField) := by
    simpa only [map_natCast] using
      hn.map ((algebraMap B Q.ResidueField).comp (algebraMap A B))
  have hcoprime := natCast_isUnit_coprime_ringExpChar Q.ResidueField n hnQ
  obtain ⟨a, ha⟩ := finiteIdealNormalizationExponent_exists_expChar_pow A B Q hQ
  rw [ha]
  exact hcoprime.pow_right a

end EtaleFundamentalGroups.Inertia
