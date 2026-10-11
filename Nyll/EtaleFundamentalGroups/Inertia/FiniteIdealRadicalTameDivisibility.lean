/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameFactorization
import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealWildPrimary
import Nyll.EtaleFundamentalGroups.Inertia.TameOrderDivisibility
import Nyll.EtaleFundamentalGroups.Inertia.UniformizerRadicalRamification
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Actual uniformizer radicals divide the actual finite tame order

The principal-unit kernel at the original prime has the power order proved
by its actual localized automorphisms. An invertible radical exponent is
coprime to that same residue characteristic, so it survives the genuine
inertia cardinality factorization, including inseparable residue extensions.

Reference: https://stacks.math.columbia.edu/tag/0BUB
-/

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- Base invertibility implies coprimality to the characteristic of the
actual prime residue field through the literal coefficient RingHom. -/
private theorem natCast_isUnit_coprime_idealResidue
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (Q : Ideal B) [Q.IsPrime] (n : ℕ) (hn : IsUnit (n : A)) :
    Nat.Coprime n (ringExpChar Q.ResidueField) := by
  let f : A →+* Q.ResidueField :=
    (IsLocalRing.residue (Localization.AtPrime Q)).comp
      ((algebraMap B (Localization.AtPrime Q)).comp (algebraMap A B))
  have hnQ : IsUnit (n : Q.ResidueField) := by
    simpa only [map_natCast] using hn.map f
  exact natCast_isUnit_coprime_ringExpChar Q.ResidueField n hnQ

/-- An actual root of a base uniformizer forces its invertible exponent to
divide the actual tame order for the intrinsic coefficient automorphisms.
The wild power and inertia cardinality are supplied by their proved owners. -/
theorem radical_exponent_dvd_finiteIdealTameOrder
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [IsGaloisGroup (B ≃ₐ[A] B) A B]
    (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver (IsLocalRing.maximalIdeal A)]
    (hQ : Q ≠ ⊥) (n : ℕ) (hn : IsUnit (n : A))
    (π : A) (hπ : Irreducible π) (γ : B)
    (hγ : γ ^ n = algebraMap A B π) :
    n ∣ finiteIdealTameOrder B (B ≃ₐ[A] B) Q hQ := by
  have hnzero : n ≠ 0 := by
    intro hz
    apply hn.ne_zero
    rw [hz, Nat.cast_zero]
  have he : n ∣ Q.ramificationIdx A :=
    exponent_dvd_ramificationIdx_of_uniformizer_pow_eq Q π hπ n hnzero γ hγ
  obtain ⟨r, hr⟩ := finiteIdealWildOrder_exists_expChar_pow A B Q hQ
  have hcoprime : Nat.Coprime n (finiteIdealWildOrder B (B ≃ₐ[A] B) Q hQ) := by
    rw [hr]
    exact (natCast_isUnit_coprime_idealResidue A B Q n hn).pow_right r
  obtain ⟨f, hf⟩ :=
    finiteIdealTameOrder_mul_wildOrder_eq_ramificationIdx_mul A B Q hQ (B ≃ₐ[A] B)
  apply hcoprime.dvd_of_dvd_mul_right
  rw [hf]
  exact he.trans (dvd_mul_right (Q.ramificationIdx A) f)

end EtaleFundamentalGroups.Inertia
