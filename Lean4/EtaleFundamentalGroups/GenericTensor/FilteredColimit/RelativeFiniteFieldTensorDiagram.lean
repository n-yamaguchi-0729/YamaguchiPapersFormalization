/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GenericTensor.FilteredColimit.FiniteFieldTensorDiagram
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Relative finite constant-extension tensor diagrams

Fix an actual finite intermediate field `F₀`. The upper interval of finite
fields containing `F₀` is `Under F₀`, since the original index is a preorder.
Each stage is the literal tensor ring `R ⊗[k] E`, read under `R ⊗[k] F₀`
through the tensor map of the actual field inclusion. Finality of the upper
interval preserves the existing tensor colimit; no coefficient lifting or
injectivity argument is repeated.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace EtaleFundamentalGroups

variable (k L R : Type u) [Field k] [Field L] [CommRing R]
variable [Algebra k L] [Algebra k R]

private def finiteIntermediateFieldTensorRingDiagram :
    FiniteIntermediateFieldIndex k L ⥤ CommRingCat.{u} :=
  finiteIntermediateFieldTensorDiagram k L R ⋙ Under.forget (CommRingCat.of R)

private def finiteIntermediateFieldTensorRingCocone :
    Cocone (finiteIntermediateFieldTensorRingDiagram k L R) :=
  (Under.forget (CommRingCat.of R)).mapCocone
    (finiteIntermediateFieldTensorCocone k L R)

/-- The actual finite constant extensions containing the fixed field `F₀`,
read as a diagram of algebras under its tensor ring. -/
def relativeFiniteIntermediateFieldTensorDiagram (F₀ : FiniteIntermediateFieldIndex k L) :
    Under F₀ ⥤ Under (CommRingCat.of (R ⊗[k] F₀.val.toSubalgebra)) :=
  Under.post (X := F₀) (finiteIntermediateFieldTensorRingDiagram k L R)

/-- The literal inclusions of all larger finite constant extensions into
`R ⊗[k] L`, with the fixed `F₀`-tensor ring as their base. -/
def relativeFiniteIntermediateFieldTensorCocone (F₀ : FiniteIntermediateFieldIndex k L) :
    Cocone (relativeFiniteIntermediateFieldTensorDiagram k L R F₀) :=
  (finiteIntermediateFieldTensorRingCocone k L R).underPost F₀

/-- The relative constant-extension cocone is colimiting, by restricting the
existing finite-field tensor colimit to the final upper interval. -/
def relativeFiniteIntermediateFieldTensorCoconeIsColimit [Algebra.IsAlgebraic k L]
    (F₀ : FiniteIntermediateFieldIndex k L) :
    IsColimit (relativeFiniteIntermediateFieldTensorCocone k L R F₀) := by
  letI : IsConnected (FiniteIntermediateFieldIndex k L) := IsFiltered.isConnected _
  have hc : IsColimit (finiteIntermediateFieldTensorRingCocone k L R) :=
    isColimitOfPreserves (Under.forget (CommRingCat.of R))
      (finiteIntermediateFieldTensorCoconeIsColimit k L R)
  exact hc.underPost F₀

/-- The relative stage algebra map is the literal tensor map of `F₀ ≤ E`. -/
theorem relativeFiniteIntermediateFieldTensorDiagram_obj_hom
    (F₀ : FiniteIntermediateFieldIndex k L) (E : Under F₀) :
    ((relativeFiniteIntermediateFieldTensorDiagram k L R F₀).obj E).hom.hom =
      (Algebra.TensorProduct.map (AlgHom.id R R)
        (Subalgebra.inclusion
          (show F₀.val.toSubalgebra ≤ E.right.val.toSubalgebra from E.hom.le))).toRingHom := by
  rfl

/-- The relative colimit point carries the literal tensor inclusion of `F₀` into `L`. -/
theorem relativeFiniteIntermediateFieldTensorCocone_pt_hom
    (F₀ : FiniteIntermediateFieldIndex k L) :
    (relativeFiniteIntermediateFieldTensorCocone k L R F₀).pt.hom.hom =
      (Algebra.TensorProduct.map (AlgHom.id R R) F₀.val.toSubalgebra.val).toRingHom := by
  rfl

/-- The relative cocone leg is the literal tensor inclusion of the stage field into `L`. -/
theorem relativeFiniteIntermediateFieldTensorCocone_leg_hom
    (F₀ : FiniteIntermediateFieldIndex k L) (E : Under F₀) :
    ((relativeFiniteIntermediateFieldTensorCocone k L R F₀).ι.app E).right.hom =
      (Algebra.TensorProduct.map (AlgHom.id R R) E.right.val.toSubalgebra.val).toRingHom := by
  rfl

end EtaleFundamentalGroups

end
