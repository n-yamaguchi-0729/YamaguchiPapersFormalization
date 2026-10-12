/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.RationalKummer
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The cyclic Galois group of a two-branch rational cover

In characteristic zero, a finite extension of an algebraically closed rational function field
unramified away from two places is Galois and cyclic. Its actual automorphism group identifies
with the degree-th roots of unity in the constant field, and this identification acts by scaling
a generating coordinate. The power-coordinate theorem supplies the Kummer generator; neither
normality nor cyclicity is assumed.
-/

noncomputable section

open AlgebraicCurve Polynomial

namespace AnabelianGeometry.GeometricFundamentalGroup

/-- A two-branch rational function-field cover in characteristic zero is cyclic Galois, with
its automorphisms acting on a generating coordinate through roots of unity in the constant field. -/
theorem cyclic_galois_of_two_branches_charZero
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F]
    (v₀ v₁ : Place K (RatFunc K)) (hne : v₀ ≠ v₁)
    (hunramified : ∀ w : Place K F, w.restrict (RatFunc K) ≠ v₀ →
      w.restrict (RatFunc K) ≠ v₁ → w.ramificationIndex (RatFunc K) = 1) :
    IsGalois (RatFunc K) F ∧ IsCyclic (F ≃ₐ[RatFunc K] F) ∧
      ∃ t : F, ∃ e : (F ≃ₐ[RatFunc K] F) ≃* rootsOfUnity (Module.finrank (RatFunc K) F) K,
        IntermediateField.adjoin K ({t} : Set F) = ⊤ ∧
        ∀ σ : F ≃ₐ[RatFunc K] F, σ t = algebraMap K F ((e σ : Kˣ) : K) * t := by
  obtain ⟨s, t, -, htgen, hpow⟩ :=
    exists_power_coordinates_of_two_branches_charZero v₀ v₁ hne hunramified
  let n : ℕ := Module.finrank (RatFunc K) F
  have hn : 0 < n := Module.finrank_pos
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero (n : K) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have hK : (primitiveRoots n K).Nonempty := ⟨ζ, (mem_primitiveRoots hn).mpr hζ⟩
  have hE : (primitiveRoots n (RatFunc K)).Nonempty :=
    ⟨algebraMap K (RatFunc K) ζ, (mem_primitiveRoots hn).mpr
      (hζ.map_of_injective (algebraMap K (RatFunc K)).injective)⟩
  have htE : IntermediateField.adjoin (RatFunc K) ({t} : Set F) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_adjoin_eq_top K htgen
  have hroot : t ^ n = algebraMap (RatFunc K) F s := hpow.symm
  have hirr : Irreducible (X ^ n - C s) :=
    irreducible_X_pow_sub_C_of_root_adjoin_eq_top hroot htE
  have hspl : IsSplittingField (RatFunc K) F (X ^ n - C s) :=
    isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hE hroot htE
  have hgal : IsGalois (RatFunc K) F := isGalois_of_isSplittingField_X_pow_sub_C hE hirr F
  have hcyc : IsCyclic (F ≃ₐ[RatFunc K] F) :=
    isCyclic_of_isSplittingField_X_pow_sub_C hE hirr F
  let eE : (F ≃ₐ[RatFunc K] F) ≃* rootsOfUnity n (RatFunc K) :=
    autEquivRootsOfUnity hE hirr F
  let eK : rootsOfUnity n K ≃* rootsOfUnity n (RatFunc K) :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap K (RatFunc K)).injective hK
  refine ⟨hgal, hcyc, t, eE.trans eK.symm, htgen, ?_⟩
  intro σ
  have hscale := autEquivRootsOfUnity_smul hE hirr F hroot σ
  simp only [Subgroup.smul_def, Units.smul_def, Algebra.smul_def] at hscale
  change algebraMap (RatFunc K) F ((eE σ : (RatFunc K)ˣ) : RatFunc K) * t = σ t at hscale
  have hconstant : algebraMap K (RatFunc K) ((eK.symm (eE σ) : Kˣ) : K) =
      ((eE σ : (RatFunc K)ˣ) : RatFunc K) :=
    rootsOfUnityEquivOfPrimitiveRoots_symm_apply (algebraMap K (RatFunc K)).injective hK (eE σ)
  rw [← hscale, ← hconstant, ← IsScalarTower.algebraMap_apply]
  rfl

end AnabelianGeometry.GeometricFundamentalGroup
