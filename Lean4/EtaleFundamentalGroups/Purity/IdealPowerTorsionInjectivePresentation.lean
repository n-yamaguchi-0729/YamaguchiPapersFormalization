/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.EssentialIdealPowerTorsion
import EtaleFundamentalGroups.Purity.ModuleInjectiveHull
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Injective presentations preserving ideal-power torsion

The injective hull of an ideal-power torsion module over a Noetherian ring
is again ideal-power torsion because its embedded image is essential.
The quotient inherits power torsion from the hull.  The inclusion and the
quotient map form a concrete short exact coefficient complex.
-/

namespace EtaleFundamentalGroups.Purity

open CategoryTheory

universe u

variable {R : Type u} [CommRing R]

/-- The coefficient complex associated with a linear map into a module.
Its objects are definitionally `M`, `E`, and `E ⧸ LinearMap.range i`. -/
def injectivePresentationShortComplex
    {M E : ModuleCat.{u} R} (i : M →ₗ[R] E) :
    ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero i (Submodule.mkQ (LinearMap.range i))
    i.exact_map_mkQ_range.linearMap_comp_eq_zero

/-- An injective linear map and its range quotient form a short exact
coefficient complex. -/
theorem injectivePresentationShortComplex_shortExact
    {M E : ModuleCat.{u} R} (i : M →ₗ[R] E) (hi : Function.Injective i) :
    (injectivePresentationShortComplex i).ShortExact :=
  ModuleCat.shortComplex_shortExact (injectivePresentationShortComplex i)
    i.exact_map_mkQ_range hi (Submodule.mkQ_surjective (LinearMap.range i))

/-- Every ideal-power torsion module over a Noetherian ring embeds into
an injective ideal-power torsion module with ideal-power torsion quotient. -/
theorem exists_idealPowerTorsion_injective_presentation
    [IsNoetherianRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (hM : ∀ z : M, ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0) :
    ∃ (E : ModuleCat.{u} R) (i : M →ₗ[R] E),
      Function.Injective i ∧ Module.Injective R E ∧
        (∀ z : E, ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0) ∧
        (∀ z : E ⧸ LinearMap.range i,
          ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0) := by
  obtain ⟨E, i, hi, hess, hEinj⟩ := exists_module_injective_hull M
  have hRange : ∀ z : LinearMap.range i,
      ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0 := by
    intro z
    obtain ⟨w, hw⟩ := z.property
    obtain ⟨n, hn⟩ := hM w
    refine ⟨n, ?_⟩
    intro a ha
    apply Subtype.ext
    change a • (z : E) = 0
    simpa only [map_smul, map_zero, hw] using congrArg i (hn a ha)
  have hE : ∀ z : E, ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0 :=
    exists_ideal_pow_smul_eq_zero_of_essential_submodule
      I (LinearMap.range i) hess hRange
  refine ⟨E, i, hi, hEinj, hE, ?_⟩
  intro z
  obtain ⟨w, rfl⟩ := (LinearMap.range i).mkQ_surjective z
  obtain ⟨n, hn⟩ := hE w
  refine ⟨n, ?_⟩
  intro a ha
  simpa only [map_smul, map_zero] using
    congrArg (Submodule.mkQ (LinearMap.range i)) (hn a ha)

end EtaleFundamentalGroups.Purity
