/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualTameRootsTopology
import EtaleFundamentalGroups.Inertia.ActualTameCharacter
import EtaleFundamentalGroups.Inertia.ActualTameCharacterContinuity
import Mathlib.Algebra.Category.Grp.Basic

/-!
# The SAME tame roots limit as its native group object

The carrier, group, and topology are exactly those of the existing actual
roots limit. This native object is shared by the quotient isomorphism and
the original decomposition action, so neither must reopen the raw index.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory CategoryTheory

universe u v w

attribute [local instance] Ideal.Quotient.field

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- The existing actual limit, retaining its existing coordinatewise group. -/
def actualTameRootsGroup : GrpCat.{w} :=
  GrpCat.of (actualFiniteTameRootsSystem A K L Q).inverseLimit

/-- The topology is literally the topology of the existing actual limit. -/
instance actualTameRootsGroup_topologicalSpace :
    TopologicalSpace (actualTameRootsGroup A K L Q).carrier :=
  inferInstanceAs (TopologicalSpace (actualFiniteTameRootsSystem A K L Q).inverseLimit)

instance actualTameRootsGroup_t2Space :
    T2Space (actualTameRootsGroup A K L Q).carrier :=
  actualFiniteTameRootsSystem_t2Space A K L Q

instance actualTameRootsGroup_isTopologicalGroup :
    IsTopologicalGroup (actualTameRootsGroup A K L Q).carrier :=
  actualFiniteTameRootsSystem_isTopologicalGroup A K L Q

/-- The SAME constructed character as a morphism of the native group objects. -/
def actualTameCharacterMorphism :
    actualNormalizationInertiaGroup A K L Q ⟶ actualTameRootsGroup A K L Q :=
  GrpCat.ofHom (actualTameCharacter A K L Q)

/-- The literal coefficient of an element of the SAME actual roots group. -/
def actualTameRootsScalar
    (n : Subtype (actualFiniteTameDegreeSet A K L Q))
    (x : (actualTameRootsGroup A K L Q).carrier) :
    (normalizationCommAlgCat A L).carrier ⧸ Q :=
  ((actualFiniteTameRootsSystem A K L Q).projection n x).val.val

/-- Literal scalar coordinates jointly separate points of the native group. -/
theorem actualTameRootsScalar_ext
    (x y : (actualTameRootsGroup A K L Q).carrier)
    (h : ∀ n : Subtype (actualFiniteTameDegreeSet A K L Q),
      actualTameRootsScalar A K L Q n x = actualTameRootsScalar A K L Q n y) :
    x = y := by
  apply (actualFiniteTameRootsSystem A K L Q).ext
  intro n
  apply rootsOfUnity.coe_injective
  exact h n

/-- Continuity of the exact stored character between the two native groups. -/
theorem actualTameCharacterMorphism_continuous :
    Continuous (actualTameCharacterMorphism A K L Q).hom'.toFun :=
  actualTameCharacter_continuous A K L Q

/-- Native scalar evaluation of the SAME character is its existing actual coordinate. -/
theorem actualTameRootsScalar_character
    (n : Subtype (actualFiniteTameDegreeSet A K L Q))
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    actualTameRootsScalar A K L Q n
        ((actualTameCharacterMorphism A K L Q).hom'.toFun σ) =
      ((actualTameCoordinate A K L Q n).toFun σ).val.val := by
  exact congrArg (fun z : (actualFiniteTameRootsSystem A K L Q).X n => z.val.val)
    (actualTameCharacter_projection A K L Q n σ)


end EtaleFundamentalGroups.Inertia

end
