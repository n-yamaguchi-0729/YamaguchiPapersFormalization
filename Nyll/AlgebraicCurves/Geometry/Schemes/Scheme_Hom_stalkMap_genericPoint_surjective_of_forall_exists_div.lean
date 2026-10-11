/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_stalkMap_genericPoint_surjective_of_forall_exists_div.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Scheme Hom stalk Map generic Point surjective of forall exists div
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_Hom_stalkMap_genericPoint_surjective_of_forall_exists_div

universe u

open CategoryTheory AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Hom.stalkMap_genericPoint_surjective_of_forall_exists_div
    {Y Z : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Z) (V : Z.Opens) (hV : f (genericPoint Y) ∈ V)
    (hgen : ∀ x : Y.functionField, ∃ a b : Γ(Z, V),
      Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V b) ≠ 0 ∧
        x * Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V b) =
          Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V a)) :
    Function.Surjective (f.stalkMap (genericPoint Y)) := by
  intro x
  obtain ⟨a, b, hb, hx⟩ := hgen x
  let ga := Z.presheaf.germ V (f (genericPoint Y)) hV a
  let gb := Z.presheaf.germ V (f (genericPoint Y)) hV b
  have hga : f.stalkMap (genericPoint Y) ga = Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app
    V a) :=
    Scheme.Hom.germ_stalkMap_apply f V (genericPoint Y) hV a
  have hgb : f.stalkMap (genericPoint Y) gb = Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app
    V b) :=
    Scheme.Hom.germ_stalkMap_apply f V (genericPoint Y) hV b
  have hunit : IsUnit gb := by
    by_contra h
    have h0 : f.stalkMap (genericPoint Y) gb = 0 := by
      have hnu : ¬ IsUnit (f.stalkMap (genericPoint Y) gb) := fun hu => h ((isUnit_map_iff _ _).mp
        hu)
      rwa [isUnit_iff_ne_zero, not_not] at hnu
    exact hb (hgb ▸ h0)
  refine ⟨ga * ↑(hunit.unit⁻¹), ?_⟩
  rw [map_mul, hga]
  have hinv : f.stalkMap (genericPoint Y) ↑(hunit.unit⁻¹) = (f.stalkMap (genericPoint Y) gb)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, IsUnit.val_inv_mul, map_one])
  rw [hinv, hgb, eq_comm, eq_mul_inv_iff_mul_eq₀ hb, hx]

end Scheme_Hom_stalkMap_genericPoint_surjective_of_forall_exists_div
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
