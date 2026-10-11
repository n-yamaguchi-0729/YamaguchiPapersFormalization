/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.FinitePowerTorsionLength
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Removing maximal-ideal-power torsion

The primary component of a finite module over a Noetherian ring has a
uniform annihilating ideal power.  If a quotient vector is killed by
another power, the product of those two powers kills any lift.  The lift
therefore already lies in the primary component, and the quotient vector
is zero.

For the maximal ideal of a local ring, this excludes the maximal ideal
from the associated primes of the quotient.
-/

namespace EtaleFundamentalGroups.Purity

universe u v

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Quotienting a finite module by its ideal-primary component removes
all vectors annihilated by powers of that ideal. -/
theorem eq_zero_of_idealPower_torsion_quotient_primaryComponent
    (I : Ideal R) (q : M ⧸ Ideal.primaryComponent M I)
    (hq : ∃ n : ℕ, ∀ a ∈ I ^ n, a • q = 0) : q = 0 := by
  let T : Submodule R M := Ideal.primaryComponent M I
  have hT : ∀ z : T, ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0 := by
    intro z
    obtain ⟨n, hn⟩ :=
      (Ideal.primaryComponent_mem (M := M) (I := I) (z : M)).mp z.property
    refine ⟨n, ?_⟩
    intro a ha
    apply Subtype.ext
    exact (Submodule.mem_torsionBySet_iff ((I ^ n : Ideal R) : Set R) (z : M)).mp hn ⟨a, ha⟩
  obtain ⟨k, hk⟩ := exists_ideal_pow_le_annihilator_of_finite I hT
  obtain ⟨z, rfl⟩ := T.mkQ_surjective q
  obtain ⟨n, hn⟩ := hq
  have hproduct : I ^ k * I ^ n ≤ (⊥ : Submodule R M).colon {z} := by
    apply Ideal.mul_le.mpr
    intro a ha b hb
    have hbT : b • z ∈ T := by
      apply (Submodule.Quotient.mk_eq_zero T).mp
      change T.mkQ (b • z) = 0
      rw [map_smul]
      exact hn b hb
    have hab : a • (⟨b • z, hbT⟩ : T) = 0 :=
      Module.mem_annihilator.mp (hk ha) ⟨b • z, hbT⟩
    apply Submodule.mem_colon_singleton.mpr
    apply (Submodule.mem_bot R).mpr
    rw [mul_smul]
    exact congrArg Subtype.val hab
  have hpower : I ^ (k + n) ≤ (⊥ : Submodule R M).colon {z} := by
    rw [pow_add]
    exact hproduct
  apply (Submodule.Quotient.mk_eq_zero T).mpr
  apply (Ideal.primaryComponent_mem (M := M) (I := I) z).mpr
  refine ⟨k + n, (Submodule.mem_torsionBySet_iff ((I ^ (k + n) : Ideal R) : Set R) z).mpr ?_⟩
  intro a
  exact (Submodule.mem_bot R).mp
    (Submodule.mem_colon_singleton.mp (hpower a.property))

/-- The maximal ideal is not associated to the quotient by the
maximal-ideal-primary component of a finite module. -/
theorem maximalIdeal_not_mem_associatedPrimes_quotient_primaryComponent
    [IsLocalRing R] :
    IsLocalRing.maximalIdeal R ∉
      associatedPrimes R (M ⧸ Ideal.primaryComponent M (IsLocalRing.maximalIdeal R)) := by
  intro hass
  have hAssociated : IsAssociatedPrime (IsLocalRing.maximalIdeal R)
      (M ⧸ Ideal.primaryComponent M (IsLocalRing.maximalIdeal R)) := hass
  obtain ⟨hprime, q, hq⟩ := isAssociatedPrime_iff.mp hAssociated
  have hqT : ∃ n : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal R ^ n, a • q = 0 := by
    refine ⟨1, ?_⟩
    intro a ha
    rw [pow_one] at ha
    rw [hq] at ha
    exact (Submodule.mem_bot R).mp (Submodule.mem_colon_singleton.mp ha)
  have hqZero : q = 0 :=
    eq_zero_of_idealPower_torsion_quotient_primaryComponent
      (IsLocalRing.maximalIdeal R) q hqT
  have hOneColon : (1 : R) ∈
      (⊥ : Submodule R
        (M ⧸ Ideal.primaryComponent M (IsLocalRing.maximalIdeal R))).colon {q} := by
    apply Submodule.mem_colon_singleton.mpr
    simpa only [hqZero, smul_zero] using
      (Submodule.zero_mem (⊥ : Submodule R
        (M ⧸ Ideal.primaryComponent M (IsLocalRing.maximalIdeal R))))
  exact hprime.one_notMem (hq.symm ▸ hOneColon)

end EtaleFundamentalGroups.Purity
