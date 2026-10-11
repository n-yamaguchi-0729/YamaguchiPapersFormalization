/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NativeIdealInertiaConjugate
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Ideal inertia included into its actual stabilizer

The subgroup order and pointwise ideal-action interfaces are closed here,
with only a ring and its acting group. The map is the literal inclusion.
-/

namespace EtaleFundamentalGroups.Inertia

open scoped Pointwise

universe u v

/-- The standard subgroup inclusion supplied by actual inertia stability. -/
def nativeIdealInertiaToStabilizer
    (B : Type u) [CommRing B] (G : Type v) [Group G] [MulSemiringAction G B]
    (Q : Ideal B) : Q.inertia G →* MulAction.stabilizer G Q :=
  Subgroup.inclusion (Ideal.inertia_le_stabilizer (M := G) Q)

/-- This literal inclusion identifies the native conjugate with stabilizer conjugation. -/
theorem nativeIdealInertiaToStabilizer_conjugate
    (B : Type u) [CommRing B] (G : Type v) [Group G] [MulSemiringAction G B]
    (Q : Ideal B) (d : MulAction.stabilizer G Q) (σ : Q.inertia G) :
    (nativeIdealInertiaToStabilizer B G Q).toFun
        (nativeIdealInertiaConjugate B G Q d σ) =
      d * (nativeIdealInertiaToStabilizer B G Q).toFun σ * d⁻¹ := by
  apply Subtype.ext
  exact nativeIdealInertiaConjugate_value B G Q d σ

/-- The literal ideal-inertia inclusion is injective. -/
theorem nativeIdealInertiaToStabilizer_injective
    (B : Type u) [CommRing B] (G : Type v) [Group G] [MulSemiringAction G B]
    (Q : Ideal B) : Function.Injective (nativeIdealInertiaToStabilizer B G Q).toFun :=
  Subgroup.inclusion_injective (Ideal.inertia_le_stabilizer (M := G) Q)

/-- Its range has exactly the original inertia image in the acting group. -/
theorem nativeIdealInertiaToStabilizer_range_map
    (B : Type u) [CommRing B] (G : Type v) [Group G] [MulSemiringAction G B]
    (Q : Ideal B) :
    (nativeIdealInertiaToStabilizer B G Q).range.map
        (MulAction.stabilizer G Q).subtype = Q.inertia G := by
  rw [MonoidHom.map_range]
  change ((MulAction.stabilizer G Q).subtype.comp
    (Subgroup.inclusion (Ideal.inertia_le_stabilizer (M := G) Q))).range = Q.inertia G
  rw [Subgroup.subtype_comp_inclusion, Subgroup.range_subtype]

end EtaleFundamentalGroups.Inertia
