/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FunctionFields.Functoriality
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Naturality of the actual generic point

The canonical function-field map commutes with the maps from the generic
stalk spectra. This is used when comparing the actual Kummer characters
on an open curve with geometric pullback from its compactification.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AnabelianGeometry.WeightFiltration

private theorem specMap_stalk_eqToHom_comp
    {X : Scheme} {x y : X} (h : x = y) :
    Spec.map (eqToHom (congrArg (fun z => X.presheaf.stalk z) h)) ≫
      X.fromSpecStalk x = X.fromSpecStalk y := by
  subst y
  simp only [eqToHom_refl, Spec.map_id, Category.id_comp]

/-- The actual generic-point square of a dominant morphism commutes. -/
theorem functionFieldMap_genericPoint
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (hf : DenseRange f) :
    Spec.map (CommRingCat.ofHom (f.functionFieldMap hf)) ≫
      X.fromSpecStalk (genericPoint X) =
        Y.fromSpecStalk (genericPoint Y) ≫ f := by
  let h : genericPoint X = f (genericPoint Y) :=
    (f.map_genericPoint_of_denseRange hf).symm
  change Spec.map (eqToHom (congrArg (fun z => X.presheaf.stalk z) h) ≫
    f.stalkMap (genericPoint Y)) ≫ X.fromSpecStalk (genericPoint X) = _
  rw [Spec.map_comp_assoc, specMap_stalk_eqToHom_comp h]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk (f := f) (x := genericPoint Y)

end AnabelianGeometry.WeightFiltration
