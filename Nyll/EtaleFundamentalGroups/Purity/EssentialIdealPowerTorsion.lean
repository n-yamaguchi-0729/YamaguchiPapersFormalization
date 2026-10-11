/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.EssentialModuleExtension
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Colon
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Ideal-power torsion in essential extensions

Over a Noetherian ring, an essential extension of an ideal-power torsion
module is again ideal-power torsion.  First, any prime annihilator in the
extension contains the ideal: otherwise an element of the ideal acts
injectively on the associated cyclic module, contradicting essentialness
and power torsion in the intersection.

Minimal primes over each element annihilator are themselves element
annihilators.  Their intersection contains the ideal, and finite
generation converts this radical containment into an annihilating power.
-/

namespace EtaleFundamentalGroups.Purity

universe u v

variable {R : Type u} [CommRing R]
variable {E : Type v} [AddCommGroup E] [Module R E]

private theorem ideal_le_prime_colon_of_essential_power_torsion
    (I : Ideal R) (N : Submodule R E) (hN : IsEssentialSubmodule N)
    (hT : ∀ z : N, ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0)
    (P : Ideal R) (hP : P.IsPrime) (y : E)
    (hPy : P = (⊥ : Submodule R E).colon {y}) :
    I ≤ P := by
  intro a ha
  by_contra haP
  have hdisjoint : Disjoint N (Submodule.span R {y}) := by
    apply Submodule.disjoint_def.mpr
    intro z hzN hzSpan
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hzSpan
    obtain ⟨n, hn⟩ := hT ⟨z, hzN⟩
    have haz : a ^ n • z = 0 :=
      congrArg Subtype.val (hn (a ^ n) (Ideal.pow_mem_pow ha n))
    have hab : a ^ n * b ∈ P := by
      rw [hPy, Submodule.mem_colon_singleton, Submodule.mem_bot]
      rw [mul_smul, hb, haz]
    have haPower : a ^ n ∉ P := fun h ↦ haP (hP.mem_of_pow_mem n h)
    have hbP : b ∈ P := (hP.mem_or_mem hab).resolve_left haPower
    have hby : b • y = 0 := by
      rw [hPy, Submodule.mem_colon_singleton, Submodule.mem_bot] at hbP
      exact hbP
    exact hb.symm.trans hby
  have hspan : Submodule.span R {y} = ⊥ :=
    hN (Submodule.span R {y}) hdisjoint
  have hy : y ∈ (⊥ : Submodule R E) :=
    hspan ▸ Submodule.mem_span_singleton_self y
  have hOne : (1 : R) ∈ P := by
    rw [hPy, Submodule.mem_colon_singleton]
    simpa only [one_smul] using hy
  exact hP.one_notMem hOne

/-- Over a Noetherian ring, every vector in an essential extension of an
ideal-power torsion module is killed by some power of that ideal. -/
theorem exists_ideal_pow_smul_eq_zero_of_essential_submodule
    [IsNoetherianRing R]
    (I : Ideal R) (N : Submodule R E) (hN : IsEssentialSubmodule N)
    (hT : ∀ z : N, ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0) (z : E) :
    ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0 := by
  let J : Ideal R := (⊥ : Submodule R E).colon {z}
  have hrad : I ≤ J.radical := by
    rw [← J.sInf_minimalPrimes]
    apply le_sInf
    intro P hP
    obtain ⟨y, hPy⟩ :=
      Submodule.exists_eq_colon_of_mem_minimalPrimes
        (N := (⊥ : Submodule R E)) (x := z) hP
    exact ideal_le_prime_colon_of_essential_power_torsion
      I N hN hT P hP.isPrime y hPy
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    I.fg_of_isNoetherianRing
  refine ⟨n, ?_⟩
  intro a ha
  have haz : a ∈ (⊥ : Submodule R E).colon {z} := hn ha
  exact (Submodule.mem_bot R).mp (Submodule.mem_colon_singleton.mp haz)

end EtaleFundamentalGroups.Purity
