/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.End

/-!
# Equivariant actions

The unnumbered equivariant-action observation in Section 1 of [Yamaguchi, arXiv:2610.05634v1](https://arxiv.org/abs/2610.05634v1).
-/

namespace Yamaguchi26AbfaithfulGalois

universe u v w x

/-- An equivariant injection `B ↪ A` and equivariant surjection `B ↠ C`
give `ker(ρA) ≤ ker(ρB) ≤ ker(ρC)`. The remaining conjuncts state the
nontriviality, faithfulness, and triviality consequences in the observation. -/
theorem equivariant_action_kernels
    {Q : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Group Q] [Group A] [Group B] [Group C]
    (ρA : Q →* MulAut A) (ρB : Q →* MulAut B) (ρC : Q →* MulAut C)
    (i : B →* A) (hi : Function.Injective i)
    (s : B →* C) (hs : Function.Surjective s)
    (hi_equivariant : ∀ (q : Q) (b : B), i (ρB q b) = ρA q (i b))
    (hs_equivariant : ∀ (q : Q) (b : B), s (ρB q b) = ρC q (s b)) :
    (∀ q : Q, ρA q = 1 → ρB q = 1) ∧
      (∀ q : Q, ρB q = 1 → ρC q = 1) ∧
      ((∃ q : Q, ρC q ≠ 1) → ∃ q : Q, ρA q ≠ 1) ∧
      (Function.Injective ρC → Function.Injective ρA) ∧
      ((∀ q : Q, ρA q = 1) → ∀ q : Q, ρC q = 1) := by
  have hAB : ∀ q : Q, ρA q = 1 → ρB q = 1 := by
    intro q hA
    apply MulEquiv.ext
    intro b
    apply hi
    calc
      i (ρB q b) = ρA q (i b) := hi_equivariant q b
      _ = i b := by rw [hA]; rfl
  have hBC : ∀ q : Q, ρB q = 1 → ρC q = 1 := by
    intro q hB
    apply MulEquiv.ext
    intro c
    obtain ⟨b, rfl⟩ := hs c
    calc
      ρC q (s b) = s (ρB q b) := (hs_equivariant q b).symm
      _ = s b := by rw [hB]; rfl
  refine ⟨hAB, hBC, ?_, ?_, ?_⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, fun hA => hq (hBC q (hAB q hA))⟩
  · intro hC x y hxy
    have hA : ρA (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hCxy := hBC (x * y⁻¹) (hAB (x * y⁻¹) hA)
    rw [map_mul, map_inv, mul_inv_eq_one] at hCxy
    exact hC hCxy
  · intro hA q
    exact hBC q (hAB q (hA q))

end Yamaguchi26AbfaithfulGalois
