/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteGaloisRestrictionGroupMap
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.FieldTheory.Normal.Defs

/-!
# Coefficient squares for finite field restriction

Defines the finite intermediate field ring object, its ambient inclusion, and individual Galois
restriction maps, and proves their commuting square.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

/-- The actual finite field as a native coefficient ring. -/
def finiteIntermediateRingObject (E : FiniteGaloisIntermediateField K L) : CommRingCat.{v} :=
  CommRingCat.of E

/-- The literal inclusion of the actual finite intermediate field. -/
def finiteIntermediateAmbientRingHom (E : FiniteGaloisIntermediateField K L) :
    finiteIntermediateRingObject K L E →+* L := E.val.toRingHom

/-- The individual actual finite field restriction, before any A-normalization. -/
def finiteGaloisRestrictionRingHom (E : FiniteGaloisIntermediateField K L)
    (σ : Gal(L/K)) :
    finiteIntermediateRingObject K L E →+* finiteIntermediateRingObject K L E :=
  (AlgEquiv.restrictNormalHom E σ).toRingHom

/-- Native field restriction before any categorical ring coercion occurs. -/
private theorem finiteGaloisRestriction_native_square (E : FiniteGaloisIntermediateField K L)
    (σ : Gal(L/K)) :
    E.val.toRingHom.comp (AlgEquiv.restrictNormalHom E σ).toRingHom =
      σ.toRingHom.comp E.val.toRingHom := by
  apply RingHom.ext
  intro x
  change algebraMap E L ((σ.restrictNormal E) x) = σ (algebraMap E L x)
  exact AlgEquiv.restrictNormal_commutes (F := K) (K₁ := L) (K₂ := L) σ E x

/-- Actual finite restriction commutes with the actual field inclusion. -/
theorem finiteGaloisRestrictionRingHom_commutes (E : FiniteGaloisIntermediateField K L)
    (σ : Gal(L/K)) :
    (finiteIntermediateAmbientRingHom K L E).comp (finiteGaloisRestrictionRingHom K L E σ) =
      σ.toRingHom.comp (finiteIntermediateAmbientRingHom K L E) :=
  finiteGaloisRestriction_native_square K L E σ

end EtaleFundamentalGroups.Inertia

end
