/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Normalizers detected by abelian images

If a subgroup embeds into an abelian image of the ambient group, its
normalizer centralizes it. This supplies the abelianization step in
self-normalization arguments for boundary inertia. No assertion about
centralizers of free profinite generators is assumed to have been proved here.
-/

namespace AnabelianGeometry.CuspidalInertia

universe u v

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]

/-- An injective abelian image forces each normalizing element to act trivially. -/
theorem normalizer_eq_centralizer_of_injective_abelian_image
    (I : Subgroup G) (f : G →* A) (hf : Set.InjOn f (I : Set G)) :
    Subgroup.normalizer (I : Set G) = Subgroup.centralizer (I : Set G) := by
  apply le_antisymm ?_ (Subgroup.centralizer_le_normalizer (I : Set G))
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hconj : g * x * g⁻¹ ∈ I := (hg x).mp hx
  have heq : g * x * g⁻¹ = x := by
    apply hf hconj hx
    simp only [map_mul, map_inv]
    rw [mul_comm (f g) (f x), mul_inv_cancel_right]
  exact (mul_inv_eq_iff_eq_mul.mp heq).symm

end AnabelianGeometry.CuspidalInertia
