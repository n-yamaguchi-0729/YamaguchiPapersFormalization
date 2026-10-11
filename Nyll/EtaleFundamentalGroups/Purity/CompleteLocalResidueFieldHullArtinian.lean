/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.EssentialModuleExtension
import Nyll.EtaleFundamentalGroups.Purity.InjectiveScalarEndomorphismArtinian
import Nyll.EtaleFundamentalGroups.Purity.MaximalIdealPowerQuotientLength
import Nyll.EtaleFundamentalGroups.Purity.ResidueFieldHullFiniteTruncation
import Nyll.EtaleFundamentalGroups.Purity.ResidueFieldHullPowerTorsion
import Mathlib.Algebra.Module.Injective
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Artinianness of a residue-field hull over a complete local ring

An endomorphism of the hull acts by a scalar on every maximal-ideal
power-torsion layer.  The scalar classes are compatible because their
differences annihilate each smaller layer.  Completeness lifts them to
one scalar in the ring, and power torsion makes its action equal to the
given endomorphism everywhere.

The scalar endomorphism theorem identifies submodules with their double
annihilators.  Noetherianity of the ring then gives the descending chain
condition on submodules of the hull.
-/

namespace EtaleFundamentalGroups.Purity

universe u

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

variable {E : Type u} [AddCommGroup E] [Module R E] [Module.Injective R E]

/-- Every endomorphism of an injective residue-field hull over a complete
Noetherian local ring is multiplication by an element of the ring. -/
theorem exists_smul_eq_of_completeLocal_residueFieldHull
    [IsAdicComplete (maximalIdeal R) R]
    (i : (R ⧸ maximalIdeal R) →ₗ[R] E) (hi : Function.Injective i)
    (hess : IsEssentialSubmodule (LinearMap.range i)) (f : E →ₗ[R] E) :
    ∃ a : R, ∀ z : E, f z = a • z := by
  classical
  choose r hr using fun n : ℕ =>
    exists_smul_eq_on_torsionBySet_of_finiteLength_quotient i hi hess
      (maximalIdeal R ^ n) (isFiniteLength_quotient_maximalIdeal_pow n) f
  have hcompat {m n : ℕ} (hmn : m ≤ n) : r m - r n ∈ maximalIdeal R ^ m := by
    apply sub_mem_ideal_of_smul_eq_zero_on_torsionBySet i hi
      (maximalIdeal R ^ m) (r m) (r n)
    intro z hz
    have hzn : ∀ a : R, a ∈ maximalIdeal R ^ n → a • z = 0 := by
      intro a ha
      exact hz a (Ideal.pow_le_pow_right hmn ha)
    rw [sub_smul, ← hr m z hz, ← hr n z hzn, sub_self]
  have hcauchy {m n : ℕ} (hmn : m ≤ n) :
      r m ≡ r n [SMOD ((maximalIdeal R ^ m) • ⊤ : Submodule R R)] := by
    apply SModEq.sub_mem.mpr
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hcompat hmn
  obtain ⟨a, ha⟩ := IsPrecomplete.prec
    (inferInstance : IsPrecomplete (maximalIdeal R) R) (f := r) hcauchy
  have hdiff (n : ℕ) : r n - a ∈ maximalIdeal R ^ n := by
    have h := SModEq.sub_mem.mp (ha n)
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using h
  refine ⟨a, ?_⟩
  intro z
  obtain ⟨n, hn⟩ :=
    exists_maximalIdeal_pow_smul_eq_zero_of_essential_residueField_range i hess z
  calc
    f z = r n • z := hr n z hn
    _ = a • z := by
      apply sub_eq_zero.mp
      rw [← sub_smul]
      exact hn (r n - a) (hdiff n)

/-- An injective hull of the residue field of a complete Noetherian local
ring is Artinian as a module over that ring. -/
theorem isArtinian_of_completeLocal_residueFieldHull
    [IsAdicComplete (maximalIdeal R) R]
    (i : (R ⧸ maximalIdeal R) →ₗ[R] E) (hi : Function.Injective i)
    (hess : IsEssentialSubmodule (LinearMap.range i)) : IsArtinian R E :=
  isArtinian_of_injective_residueField_and_scalar_endomorphisms i hi
    (exists_smul_eq_of_completeLocal_residueFieldHull i hi hess)

end EtaleFundamentalGroups.Purity
