/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.EssentialIdealPowerTorsion
import EtaleFundamentalGroups.Purity.EssentialModuleExtension
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Power torsion in an essential extension of the residue field

The residue-field image is killed by the maximal ideal.  The general
preservation of ideal-power torsion under essential extensions therefore
makes every vector in an essential extension of that image power torsion.
No injectivity assumption on the ambient module is required.
-/

namespace EtaleFundamentalGroups.Purity

universe u v

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {E : Type v} [AddCommGroup E] [Module R E]

/-- Every element of an essential extension of the residue field is
annihilated by a power of the maximal ideal.  The embedding furnished by
an injective hull supplies `i` and `hi`; its injectivity is not needed here. -/
theorem exists_maximalIdeal_pow_smul_eq_zero_of_essential_residueField_range
    [IsNoetherianRing R]
    (i : R ⧸ maximalIdeal R →ₗ[R] E)
    (hi : IsEssentialSubmodule (LinearMap.range i)) (z : E) :
    ∃ n : ℕ, ∀ a : R, a ∈ maximalIdeal R ^ n → a • z = 0 := by
  apply exists_ideal_pow_smul_eq_zero_of_essential_submodule
    (maximalIdeal R) (LinearMap.range i) hi ?_ z
  intro w
  refine ⟨1, ?_⟩
  intro a ha
  rw [pow_one] at ha
  apply Subtype.ext
  change a • (w : E) = 0
  obtain ⟨q, hq⟩ := w.property
  have haq : a • q = 0 := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    change Ideal.Quotient.mk (maximalIdeal R) (a * r) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((maximalIdeal R).mul_mem_right r ha)
  rw [← hq, ← map_smul, haq, map_zero]

end EtaleFundamentalGroups.Purity
