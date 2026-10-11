/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import ValuedFieldTheory.Ramification.HilbertRamification.RootsOfUnityFieldEmbedding
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Unique root scaling over a separably closed field

Two nonzero roots of the same invertible power over an extension field differ
by exactly one root of unity in the separably closed base field.
-/

noncomputable section

universe u v

namespace EtaleFundamentalGroups.Kummer

/-- Two nonzero roots of the same prime-to-characteristic power differ by a
unique root of unity in the separably closed base field. -/
theorem existsUnique_rootScale {K : Type u} [Field K] [IsSepClosed K]
    {Ω : Type v} [Field Ω] (ι : K →+* Ω) (n : ℕ+)
    (hn : IsUnit ((n : ℕ) : K)) (x y : Ω) (hx : x ≠ 0)
    (hxy : x ^ (n : ℕ) = y ^ (n : ℕ)) :
    ∃! ζ : rootsOfUnity (n : ℕ) K, ι ((ζ : Kˣ) : K) * x = y := by
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  have hratio : (y / x) ^ (n : ℕ) = 1 := by
    rw [div_pow, ← hxy, div_self (pow_ne_zero _ hx)]
  let η : rootsOfUnity (n : ℕ) Ω := rootsOfUnity.mkOfPowEq (y / x) hratio
  obtain ⟨ζ, hζ⟩ :=
    (RamificationTheory.HilbertRamification.restrictRootsOfUnity_bijective_of_primitiveRoot
      ι (n : ℕ) (HasEnoughRootsOfUnity.exists_primitiveRoot K (n : ℕ))).2 η
  have hζvalue : ι ((ζ : Kˣ) : K) = y / x :=
    congrArg (fun r : rootsOfUnity (n : ℕ) Ω => ((r : Ωˣ) : Ω)) hζ
  have hscale : ι ((ζ : Kˣ) : K) * x = y := by
    rw [hζvalue, div_mul_cancel₀ _ hx]
  refine ⟨ζ, hscale, ?_⟩
  intro ζ' hζ'
  apply rootsOfUnity.coe_injective
  apply ι.injective
  exact mul_right_cancel₀ hx (hζ'.trans hscale.symm)

end EtaleFundamentalGroups.Kummer
