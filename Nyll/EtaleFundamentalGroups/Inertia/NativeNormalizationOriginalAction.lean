/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.AmbientNormalizationGroupMap
import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.Algebra.Field.IsField

/-!
# Original normalization actions on native coefficient fields

The native coefficient algebra owns the ring and coefficient action. Its
field structure is opened only here. Restriction of the original field
action is compared with normalization functoriality through their literal
injective coefficient inclusion.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) [CommRing A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  (C : CommAlgCat.{w} A) (hC : IsField C.carrier)
  [Algebra K C.carrier] [tAKC : IsScalarTower A K C.carrier]
  [Algebra.IsAlgebraic K C.carrier]

/-- The prescribed integral-closure action, on the native normalization
carrier, with no finite-intermediate-field structure opened by its caller. -/
@[instance_reducible]
def nativeNormalizationOriginalAction :
    MulSemiringAction (galoisGroupObject K C.carrier).carrier
      (normalizationCommAlgCat A C.carrier).carrier := by
  let : Field C.carrier := hC.toField
  exact normalizationInertiaImageAction A K C.carrier

/-- The prescribed action agrees with the existing normalization group
map. The equality is proved on actual coefficients, rather than supplied. -/
theorem nativeNormalizationOriginalAction_ringHom
    (g : (galoisGroupObject K C.carrier).carrier) :
    let : MulSemiringAction (galoisGroupObject K C.carrier).carrier
        (normalizationCommAlgCat A C.carrier).carrier :=
      nativeNormalizationOriginalAction A K C hC
    MulSemiringAction.toRingHom (galoisGroupObject K C.carrier).carrier
        (normalizationCommAlgCat A C.carrier).carrier g =
      commAlgAutomorphismRingHom A (normalizationCommAlgCat A C.carrier)
        ((normalizationAutomorphismGroupMap A C).hom'.toFun
          ((scalarRestrictionGroupMap A K C).hom'.toFun g)) := by
  intro nativeAction
  let : Field C.carrier := hC.toField
  apply (RingHom.cancel_left (g := normalizationAmbientRingHom A C)
    Subtype.val_injective).mp
  exact (normalizationCommAlg_action_comp_inclusion A K C.carrier g).symm.trans
    (normalizationGaloisRingHom_commutes A K C.carrier g).symm

end EtaleFundamentalGroups.Inertia
