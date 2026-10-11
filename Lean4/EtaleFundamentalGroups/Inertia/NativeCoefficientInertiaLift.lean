/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import SchemeTheory.Normalization.NativeAutomorphismRingMaps

/-!
# Inertia lifts through the actual coefficient action

Surjectivity on coefficient automorphisms and the proved action comparison
transfer the literal inertia difference condition. No field or scalar
tower occurs in this argument.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v

/-- A coefficient-automorphism lift with the same actual ring action
preserves the literal inertia condition. -/
theorem coefficientInertia_exists_preimage
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) (G : GrpCat.{v})
    (Q : Ideal B.carrier) (a : MulSemiringAction G.carrier B.carrier)
    (f : GrpCat.Hom G (commAlgAutomorphismGroup A B))
    (hsurj : Function.Surjective f.hom'.toFun)
    (hcompare :
      let : MulSemiringAction G.carrier B.carrier := a
      ∀ g : G.carrier, MulSemiringAction.toRingHom G.carrier B.carrier g =
        commAlgAutomorphismRingHom A B (f.hom'.toFun g)) :
    let : MulSemiringAction G.carrier B.carrier := a
    ∀ τ : (commAlgIdealInertiaGroup A B Q).carrier,
      ∃ g : G.carrier, (Q.inertia G.carrier).carrier g ∧ f.hom'.toFun g = τ.val := by
  intro ringAction τ
  obtain ⟨g, hg⟩ := hsurj τ.val
  refine ⟨g, ?_, hg⟩
  intro b
  change Q.carrier ((MulSemiringAction.toRingHom G.carrier B.carrier g).toFun b - b)
  rw [hcompare g, hg]
  exact τ.property b

end EtaleFundamentalGroups.Inertia
