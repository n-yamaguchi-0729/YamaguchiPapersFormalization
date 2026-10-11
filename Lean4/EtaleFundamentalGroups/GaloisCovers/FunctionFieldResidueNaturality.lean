/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.LocalGeometry.HeightOne.ComponentFunctionField
import SchemeTheory.FunctionFields.Functoriality

/-!
# Naturality of generic-point residue fields

The canonical identification of the function field of an integral scheme
with the residue field at its generic point is natural for dense morphisms.
This is the comparison needed to transport tensor-product maps between
function fields to the residue-field tensor appearing in the pullback
carrier description.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Z : Scheme.{u}}

private theorem eqToHom_stalk_eq_stalkCongr
    (T : Scheme.{u}) {x x' : T} (h : x = x') :
    eqToHom (congrArg (fun q ↦ T.presheaf.stalk q) h) =
      (T.presheaf.stalkCongr (.of_eq h)).hom := by
  subst x'
  simp

/-- Identifying function fields with generic-point residue fields commutes
with the maps induced by a dense morphism of integral schemes. -/
theorem functionFieldResidueFieldRingEquiv_naturality
    [IsIntegral X] [IsIntegral Z]
    (g : Z ⟶ X) (hg : DenseRange g) :
    let hη : genericPoint X = g (genericPoint Z) :=
      (g.map_genericPoint_of_denseRange hg).symm
    CommRingCat.ofHom
        (Scheme.functionFieldResidueFieldRingEquiv X).toRingHom ≫
      (X.residueFieldCongr hη).hom ≫
      g.residueFieldMap (genericPoint Z) =
    CommRingCat.ofHom (g.functionFieldMap hg) ≫
      CommRingCat.ofHom
        (Scheme.functionFieldResidueFieldRingEquiv Z).toRingHom := by
  let hη : genericPoint X = g (genericPoint Z) :=
    (g.map_genericPoint_of_denseRange hg).symm
  change CommRingCat.ofHom
        (Scheme.functionFieldResidueFieldRingEquiv X).toRingHom ≫
      (X.residueFieldCongr hη).hom ≫
      g.residueFieldMap (genericPoint Z) =
    CommRingCat.ofHom (g.functionFieldMap hg) ≫
      CommRingCat.ofHom
        (Scheme.functionFieldResidueFieldRingEquiv Z).toRingHom
  change X.residue (genericPoint X) ≫
      (X.residueFieldCongr hη).hom ≫
      g.residueFieldMap (genericPoint Z) =
    (eqToHom (show X.presheaf.stalk (genericPoint X) =
        X.presheaf.stalk (g (genericPoint Z)) by rw [hη]) ≫
      g.stalkMap (genericPoint Z)) ≫ Z.residue (genericPoint Z)
  rw [eqToHom_stalk_eq_stalkCongr]
  · rw [Scheme.residue_residueFieldCongr_assoc]
    rw [Scheme.residue_residueFieldMap]
    simp only [Category.assoc]
  · exact hη

end AlgebraicGeometry.Scheme.Hom

