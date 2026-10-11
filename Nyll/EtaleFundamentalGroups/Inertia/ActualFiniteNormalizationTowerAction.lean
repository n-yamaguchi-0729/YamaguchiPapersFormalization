/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationTower
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationInclusionSquare
import Nyll.SchemeTheory.Normalization.AmbientNormalizationGroupMap
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Galois action on finite normalization towers

Proves that the two restricted Galois automorphisms commute with the inclusion between nested
finite normalizations.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- The two actual restricted automorphisms commute with the literal finite
normalization tower inclusion. The equation follows from their already
proved original ambient inclusion squares. -/
theorem actualFiniteNormalizationTowerRingMap_action
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) (σ : Gal(L/K)) :
    (actualFiniteNormalizationTowerRingMap A K L E F h).comp
        (actualFiniteNormalizationRestrictionRingHom A K L E σ) =
      (actualFiniteNormalizationRestrictionRingHom A K L F σ).comp
        (actualFiniteNormalizationTowerRingMap A K L E F h) := by
  let i := finiteAbsoluteNormalizationRingMap A K L F
  let j := finiteAbsoluteNormalizationRingMap A K L E
  let f := actualFiniteNormalizationTowerRingMap A K L E F h
  let s := actualFiniteNormalizationRestrictionRingHom A K L E σ
  let t := actualFiniteNormalizationRestrictionRingHom A K L F σ
  let a := normalizationGaloisRingHom A K L σ
  have hf : i.comp f = j := actualFiniteNormalizationTowerRingMap_comp A K L E F h
  have hs : j.comp s = a.comp j :=
    actualFiniteNormalizationRestrictionRingHom_inclusion A K L E σ
  have ht : i.comp t = a.comp i :=
    actualFiniteNormalizationRestrictionRingHom_inclusion A K L F σ
  apply (RingHom.cancel_left (g := i)
    (finiteAbsoluteNormalizationRingMap_injective A K L F)).mp
  calc
    i.comp (f.comp s) = (i.comp f).comp s := (RingHom.comp_assoc s f i).symm
    _ = j.comp s := congrArg (fun g => g.comp s) hf
    _ = a.comp j := hs
    _ = a.comp (i.comp f) := congrArg (fun g => a.comp g) hf.symm
    _ = (a.comp i).comp f := (RingHom.comp_assoc f i a).symm
    _ = (i.comp t).comp f := congrArg (fun g => g.comp f) ht.symm
    _ = i.comp (t.comp f) := RingHom.comp_assoc f t i

end EtaleFundamentalGroups.Inertia
