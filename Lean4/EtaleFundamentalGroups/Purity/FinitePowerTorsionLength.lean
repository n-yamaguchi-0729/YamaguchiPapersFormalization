/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.MaximalIdealPowerQuotientLength
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite length of finite maximal-ideal-power torsion modules

A finite generating set bounds the ideal-power exponents needed to kill
individual elements.  In the local Noetherian case the module is then finite
over an Artinian maximal-ideal-power quotient, so it has finite length.
-/

namespace EtaleFundamentalGroups.Purity

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Elementwise ideal-power torsion on a finite module has a uniform
annihilating exponent. -/
theorem exists_ideal_pow_le_annihilator_of_finite
    [Module.Finite R M] (I : Ideal R)
    (hM : ∀ z : M, ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0) :
    ∃ n : ℕ, I ^ n ≤ Module.annihilator R M := by
  classical
  choose n hn using hM
  obtain ⟨s, hs⟩ := (show (⊤ : Submodule R M).FG from Module.Finite.fg_top)
  refine ⟨s.sup n, ?_⟩
  intro a ha
  apply Module.mem_annihilator.mpr
  intro z
  have hspan : Submodule.span R (s : Set M) ≤
      LinearMap.ker (a • (LinearMap.id : M →ₗ[R] M)) := by
    apply Submodule.span_le.mpr
    intro y hy
    change a • y = 0
    exact hn y a (Ideal.pow_le_pow_right (Finset.le_sup hy) ha)
  rw [hs] at hspan
  exact hspan (Submodule.mem_top : z ∈ (⊤ : Submodule R M))

/-- A finite module whose elements are killed by powers of the maximal
ideal of a Noetherian local ring has finite length. -/
theorem isFiniteLength_of_finite_of_maximalIdealPower_torsion
    [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M]
    (hM : ∀ z : M, ∃ n : ℕ,
      ∀ a ∈ IsLocalRing.maximalIdeal R ^ n, a • z = 0) :
    IsFiniteLength R M := by
  obtain ⟨n, hn⟩ :=
    exists_ideal_pow_le_annihilator_of_finite (IsLocalRing.maximalIdeal R) hM
  let I : Ideal R := IsLocalRing.maximalIdeal R ^ n
  let : IsArtinian R (R ⧸ I) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (isFiniteLength_quotient_maximalIdeal_pow (R := R) n)).2
  let : IsArtinianRing (R ⧸ I) :=
    isArtinian_of_tower R (inferInstance : IsArtinian R (R ⧸ I))
  have hT : Module.IsTorsionBySet R M I :=
    (Module.isTorsionBySet_iff_subset_annihilator R M).mpr hn
  let : Module (R ⧸ I) M := hT.module
  let : Module.Finite (R ⧸ I) M :=
    Module.Finite.of_surjective hT.semilinearMap Function.surjective_id
  have hart : IsArtinian R M :=
    (LinearMap.isArtinian_iff_of_bijective
      hT.semilinearMap Function.bijective_id).mpr
      (inferInstance : IsArtinian (R ⧸ I) M)
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, hart⟩

end EtaleFundamentalGroups.Purity
