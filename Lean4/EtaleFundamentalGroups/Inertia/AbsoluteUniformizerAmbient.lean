/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AbsoluteUniformizerRadical
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# An actual finite Galois uniformizer radical in the ambient separable closure

The established finite-field radical construction is exposed through its
literal ambient element and finite-level membership. The later native
normalization owner can consume this without opening the finite field's
scalar actions alongside the original absolute prime.

Reference: Stacks Project, Tag 0BUB.
https://stacks.math.columbia.edu/tag/0BUB
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v w

/-- Retain the actual finite-field radical as an ambient element together
with its literal finite-level membership. -/
private theorem exists_finiteGalois_ambient_radical
    (K : Type v) (Ω : Type w) [Field K] [Field Ω]
    [Algebra K Ω] [IsSepClosure K Ω]
    (n : ℕ) (hn : (n : K) ≠ 0) (a : K) :
    ∃ (E : FiniteGaloisIntermediateField K Ω) (α : Ω),
      α ∈ E.toIntermediateField ∧ α ^ n = algebraMap K Ω a := by
  obtain ⟨E, β, hβ⟩ := exists_finiteGalois_radical K Ω n hn a
  refine ⟨E, (β : Ω), β.property, ?_⟩
  exact congrArg E.toIntermediateField.val hβ

/-- The original DVR and its actual separable closure produce a nonzero
integral uniformizer radical in an actual finite Galois level. Only the
ambient scalar actions occur in this endpoint. -/
theorem exists_finiteGalois_ambient_uniformizer_radical
    (A : Type u) (K : Type v) (Ω : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
    [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosure K Ω]
    (n : ℕ) (hn : IsUnit (n : A)) :
    ∃ (E : FiniteGaloisIntermediateField K Ω) (π : A) (α : Ω),
      Irreducible π ∧ α ≠ 0 ∧ α ∈ E.toIntermediateField ∧
        IsIntegral A α ∧ α ^ n = algebraMap A Ω π := by
  have hnK : IsUnit (n : K) := by
    simpa only [map_natCast] using hn.map (algebraMap A K)
  have hnzero : n ≠ 0 := by
    intro hz
    apply hnK.ne_zero
    rw [hz, Nat.cast_zero]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨E, α, hαmem, hαpow⟩ :=
    exists_finiteGalois_ambient_radical K Ω n hnK.ne_zero (algebraMap A K π)
  have hpow : α ^ n = algebraMap A Ω π :=
    hαpow.trans (IsScalarTower.algebraMap_apply A K Ω π).symm
  have hint : IsIntegral A α :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hnzero) (hpow.symm ▸ isIntegral_algebraMap)
  have hinj : Function.Injective (algebraMap A Ω) := by
    rw [IsScalarTower.algebraMap_eq A K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective A K)
  refine ⟨E, π, α, hπ, ?_, hαmem, hint, hpow⟩
  intro hαzero
  apply hπ.ne_zero
  apply hinj
  rw [map_zero, ← hpow, hαzero, zero_pow hnzero]

end EtaleFundamentalGroups.Inertia

end
