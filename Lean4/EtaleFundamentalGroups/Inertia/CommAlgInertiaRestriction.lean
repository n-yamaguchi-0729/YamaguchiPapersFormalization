/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import SchemeTheory.Normalization.NativeAutomorphismRingMaps
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.Ideal.Defs

/-!
# Inertia morphisms from coefficient differences

Constructs a group morphism into intrinsic ideal inertia from a coefficient-automorphism map
satisfying the inertia difference condition.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v

/-- The proved literal coefficient difference condition constructs the
actual map into the existing native intrinsic ideal-inertia group. -/
def commAlgInertiaHomOfDifference
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) (G : GrpCat.{v})
    (Q : Ideal B) (f : GrpCat.Hom G (commAlgAutomorphismGroup A B))
    (hf : ∀ g : G, ∀ b : B,
      Q.carrier ((commAlgAutomorphismRingHom A B (f.hom'.toFun g)).toFun b - b)) :
    GrpCat.Hom G (commAlgIdealInertiaGroup A B Q) where
  hom' :=
    { toFun := fun g => ⟨f.hom'.toFun g, hf g⟩
      map_one' := Subtype.ext f.hom'.map_one
      map_mul' := fun g h => Subtype.ext (f.hom'.map_mul g h) }

end EtaleFundamentalGroups.Inertia
