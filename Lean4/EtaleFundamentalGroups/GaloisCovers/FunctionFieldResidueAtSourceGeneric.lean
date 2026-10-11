/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.FunctionFieldResidueNaturality

/-!
# Function fields at the image of a source generic point

For a dense morphism of integral schemes, the function field of the target
is canonically the residue field at the image of the source generic point.
The resulting equivalence is compatible with the residue-field map to the
source generic point.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Z : Scheme.{u}}

/-- The target function field, identified with the residue field at the
image of the source generic point of a dense morphism. -/
noncomputable def functionFieldResidueFieldRingEquivAtSourceGeneric
    [IsIntegral X] [IsIntegral Z]
    (g : Z ⟶ X) (hg : DenseRange g) :
    X.functionField ≃+* X.residueField (g (genericPoint Z)) :=
  (Scheme.functionFieldResidueFieldRingEquiv X).trans
    (X.residueFieldCongr
      (g.map_genericPoint_of_denseRange hg).symm).commRingCatIsoToRingEquiv

/-- Naturality of the source-generic-point function-field identification. -/
theorem functionFieldResidueFieldRingEquivAtSourceGeneric_naturality
    [IsIntegral X] [IsIntegral Z]
    (g : Z ⟶ X) (hg : DenseRange g) :
    CommRingCat.ofHom
        (g.functionFieldResidueFieldRingEquivAtSourceGeneric hg).toRingHom ≫
      g.residueFieldMap (genericPoint Z) =
    CommRingCat.ofHom (g.functionFieldMap hg) ≫
      CommRingCat.ofHom
        (Scheme.functionFieldResidueFieldRingEquiv Z).toRingHom := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  have hnat := g.functionFieldResidueFieldRingEquiv_naturality hg
  have hnat' := congrArg CommRingCat.Hom.hom hnat
  simpa [functionFieldResidueFieldRingEquivAtSourceGeneric,
    Category.assoc] using DFunLike.congr_fun hnat' a

end AlgebraicGeometry.Scheme.Hom

end
