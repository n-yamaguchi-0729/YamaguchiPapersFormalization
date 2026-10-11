/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.BaseChange
import Nyll.EtaleCohomology.Sites.SetSheafFunctors
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Composition of inverse and direct image for étale sheaves of sets

Scheme-theoretic pullback pasting gives the comparison of direct images.
The inverse image comparison follows from the constructed adjunctions and
uniqueness of left adjoints. No conditions on the scheme morphisms are needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace EtaleCohomology

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Iterated direct image of set-valued étale sheaves is direct image along the composite. -/
def etaleSetPushforwardCompIso :
    etaleSetPushforward f ⋙ etaleSetPushforward g ≅ etaleSetPushforward (f ≫ g) := by
  let e : etaleBaseChange (f ≫ g) ≅ etaleBaseChange g ⋙ etaleBaseChange f :=
    MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme from @Etale) (Q := ⊤) f g
  exact Functor.sheafPushforwardContinuousComp' e.symm
    (Type u) Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology

/-- Inverse image of set-valued étale sheaves along a composite is iterated inverse image. -/
def etaleSetPullbackCompIso :
    etaleSetPullback (f ≫ g) ≅ etaleSetPullback g ⋙ etaleSetPullback f :=
  (etaleSetPullbackPushforwardAdjunction (f ≫ g)).leftAdjointUniq
    (((etaleSetPullbackPushforwardAdjunction g).comp
      (etaleSetPullbackPushforwardAdjunction f)).ofNatIsoRight
        (etaleSetPushforwardCompIso f g))

end EtaleCohomology
