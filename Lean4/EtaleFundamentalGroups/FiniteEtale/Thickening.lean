/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import SchemeTheory.FiniteEtale.ThickeningFullyFaithful
public import SchemeTheory.FiniteEtale.ThickeningGluing
public import Mathlib.CategoryTheory.Equivalence

/-!
# Invariance of finite étale covers under thickenings

A thickening is a surjective closed immersion. The affine equivalence for
nil ideals supplies unique local lifts of maps and finite étale objects.
Gluing on the directed affine cover gives the equivalence for arbitrary
schemes, without a uniform nilpotence bound or a quasicompactness assumption.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleInfStableUnderBaseChangeThickeningExport :
    MorphismProperty.IsStableUnderBaseChange
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) :=
  MorphismProperty.IsStableUnderBaseChange.inf

/-- Pullback across any thickening is an equivalence on finite étale covers. -/
@[stacks 0BQB]
theorem pullback_isEquivalence_of_surjective_closedImmersion
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] [Surjective i] :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ i).IsEquivalence where
  faithful := pullback_faithful_of_surjective_closedImmersion i
  full := pullback_full_of_surjective_closedImmersion i
  essSurj := pullback_essSurj_of_surjective_closedImmersion i

end AlgebraicGeometry.FiniteEtale
