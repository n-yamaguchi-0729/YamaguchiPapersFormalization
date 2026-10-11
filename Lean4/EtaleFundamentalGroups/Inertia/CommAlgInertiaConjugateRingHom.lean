/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgInertiaRingMaps
import EtaleFundamentalGroups.Inertia.CommAlgIdealInertiaConjugate
import EtaleFundamentalGroups.Inertia.CommAlgDecompositionGroup
import SchemeTheory.Normalization.NativeAutomorphismRingMaps

/-!
# The coefficient ring map of intrinsic inertia conjugation

Intrinsic algebra-automorphism operations are closed in this native owner.
The output uses only composition of the actual coefficient ring maps.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v

theorem commAlgIdealInertiaConjugate_ringHom
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) (Q : Ideal B.carrier)
    (d : (commAlgIdealDecompositionGroup A B Q).carrier)
    (σ : (commAlgIdealInertiaGroup A B Q).carrier) :
    commAlgIdealInertiaRingHom A B Q (commAlgIdealInertiaConjugate A B Q d σ) =
      (commAlgAutomorphismRingHom A B d.val).comp
        ((commAlgIdealInertiaRingHom A B Q σ).comp
          (commAlgAutomorphismRingHom A B (d⁻¹).val)) := by
  apply RingHom.ext
  intro b
  rfl

end EtaleFundamentalGroups.Inertia
