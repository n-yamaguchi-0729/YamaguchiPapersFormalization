/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationCoefficientSquare
import SchemeTheory.Normalization.AmbientNormalizationGroupMap
import SchemeTheory.Normalization.SubalgebraPreimage

/-!
# Finite normalization inclusion squares

Factors the finite ambient inclusion through the original normalization and proves compatibility
of this inclusion with restricted Galois automorphisms.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

omit [IsFractionRing A K] [IsGalois K L] in
/-- The literal finite-normalization inclusion factors the ambient inclusion. -/
theorem actualFiniteNormalizationAmbientRingHom_factor (E : FiniteGaloisIntermediateField K L) :
    (normalizationAmbientRingHom A (CommAlgCat.of A L)).comp
        (finiteAbsoluteNormalizationRingMap A K L E) =
      actualFiniteNormalizationAmbientRingHom A K L E := rfl

omit [IsFractionRing A K] [IsGalois K L] in
/-- The actual finite normalization restriction commutes with the literal
inclusion into the original upper normalization. -/
theorem actualFiniteNormalizationRestrictionRingHom_inclusion
    (E : FiniteGaloisIntermediateField K L) (σ : Gal(L/K)) :
    (finiteAbsoluteNormalizationRingMap A K L E).comp
        (actualFiniteNormalizationRestrictionRingHom A K L E σ) =
      (normalizationGaloisRingHom A K L σ).comp
        (finiteAbsoluteNormalizationRingMap A K L E) := by
  let i := normalizationAmbientRingHom A (CommAlgCat.of A L)
  let j := finiteAbsoluteNormalizationRingMap A K L E
  let s := actualFiniteNormalizationRestrictionRingHom A K L E σ
  let t := normalizationGaloisRingHom A K L σ
  let a := galoisAutomorphismRingHom K L σ
  have hfactor : i.comp j = actualFiniteNormalizationAmbientRingHom A K L E :=
    actualFiniteNormalizationAmbientRingHom_factor A K L E
  have hu : i.comp t = a.comp i := normalizationGaloisRingHom_commutes A K L σ
  apply (RingHom.cancel_left (g := i) Subtype.val_injective).mp
  calc
    i.comp (j.comp s) = (i.comp j).comp s := (RingHom.comp_assoc s j i).symm
    _ = (actualFiniteNormalizationAmbientRingHom A K L E).comp s :=
      congrArg (fun f => f.comp s) hfactor
    _ = a.comp (actualFiniteNormalizationAmbientRingHom A K L E) :=
      actualFiniteNormalizationRestrictionRingHom_commutes A K L E σ
    _ = a.comp (i.comp j) := congrArg (fun f => a.comp f) hfactor.symm
    _ = (a.comp i).comp j := (RingHom.comp_assoc j i a).symm
    _ = (i.comp t).comp j := congrArg (fun f => f.comp j) hu.symm
    _ = i.comp (t.comp j) := RingHom.comp_assoc j t i

end EtaleFundamentalGroups.Inertia
