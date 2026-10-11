/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Conjugation of original ideal inertia

Constructs conjugation by an ideal stabilizer element on the original ideal inertia group and
records its underlying group expression.
-/

namespace EtaleFundamentalGroups.Inertia

open scoped Pointwise

universe u v

/-- Conjugation by an actual ideal stabilizer preserves the original ideal inertia. -/
def nativeIdealInertiaConjugate
    (B : Type u) [CommRing B] (G : Type v) [Group G] [MulSemiringAction G B]
    (Q : Ideal B) (d : MulAction.stabilizer G Q) (σ : Q.inertia G) : Q.inertia G := by
  refine ⟨d.val * σ.val * d.val⁻¹, ?_⟩
  have hmem : d.val * σ.val * d.val⁻¹ ∈ (Q.inertia G).map (MulAut.conj d.val) :=
    Subgroup.mem_map.mpr ⟨σ.val, σ.property, rfl⟩
  rw [← Ideal.inertia_smul, d.property] at hmem
  exact hmem

/-- The conjugation owner retains the literal original group expression. -/
theorem nativeIdealInertiaConjugate_value
    (B : Type u) [CommRing B] (G : Type v) [Group G] [MulSemiringAction G B]
    (Q : Ideal B) (d : MulAction.stabilizer G Q) (σ : Q.inertia G) :
    (nativeIdealInertiaConjugate B G Q d σ).val = d.val * σ.val * d.val⁻¹ := rfl

end EtaleFundamentalGroups.Inertia
