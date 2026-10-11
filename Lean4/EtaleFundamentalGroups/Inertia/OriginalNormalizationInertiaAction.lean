/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Normalization.AmbientNormalizationGroupMap
import SchemeTheory.Normalization.SubalgebraPreimage
import SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Original Galois inertia on the normalization

Identifies the native normalization ring map with the original Galois action. Defines the
original inertia group and derives its coefficient difference condition.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] normalizationCommAlgGaloisAction

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

/-- The individual native normalization map is the original ramification
action, as proved by their common injective coefficient inclusion. -/
theorem normalizationGaloisRingHom_eq_original (σ : Gal(L/K)) :
    normalizationGaloisRingHom A K L σ =
      MulSemiringAction.toRingHom Gal(L/K) (normalizationCommAlgCat A L).carrier σ := by
  apply (RingHom.cancel_left (g := normalizationCommAlgInclusion A L)
    Subtype.val_injective).mp
  exact (normalizationGaloisRingHom_commutes A K L σ).trans
    (normalizationCommAlg_action_comp_inclusion A K L σ)

/-- The actual original ideal inertia, with its original Galois action. -/
def actualNormalizationInertiaGroup
    (Q : Ideal (normalizationCommAlgCat A L).carrier) : GrpCat.{w} :=
  GrpCat.of (Q.inertia Gal(L/K))

/-- The original automorphism underlying an actual ideal-inertia element. -/
def actualNormalizationInertiaElement (Q : Ideal (normalizationCommAlgCat A L).carrier)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) : Gal(L/K) := σ.val

/-- Actual original ideal inertia gives the literal difference predicate
for the canonically constructed normalization automorphism. -/
theorem actualNormalizationInertia_difference (Q : Ideal (normalizationCommAlgCat A L).carrier)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    ∀ b : (normalizationCommAlgCat A L).carrier,
      Sub.sub (α := (normalizationCommAlgCat A L).carrier)
        ((normalizationGaloisRingHom A K L (actualNormalizationInertiaElement A K L Q σ) :
          (normalizationCommAlgCat A L).carrier →+*
            (normalizationCommAlgCat A L).carrier).toFun b) b ∈ Q := by
  rw [normalizationGaloisRingHom_eq_original]
  exact σ.property

end EtaleFundamentalGroups.Inertia

end
