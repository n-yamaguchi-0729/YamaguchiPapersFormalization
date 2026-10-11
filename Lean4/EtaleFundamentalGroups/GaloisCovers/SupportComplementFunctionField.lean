/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.OpenFunctionField
import SchemeTheory.Divisors.LocalComplement

/-!
# Function fields of divisor complements

The function field of the open complement of an ideal sheaf is the ambient
function field.  The algebra structure below remembers the canonical map
from a chosen ambient stalk, which is needed for normalization at a boundary
prime.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} [IsIntegral X]

/-- The canonical algebra structure from an ambient stalk to the function
field of the support complement. -/
@[reducible]
noncomputable def supportComplementFunctionFieldAlgebra
    (I : X.IdealSheafData) [Nonempty I.supportComplement]
    (x : X) : Algebra (X.presheaf.stalk x)
      (I.supportComplement : Scheme).functionField :=
  ((I.supportComplement.ι.functionFieldRingEquivOfIsOpenImmersion.toRingHom).comp
    (algebraMap (X.presheaf.stalk x) X.functionField)).toAlgebra

/-- The canonical open-immersion function-field equivalence, as an
equivalence over the chosen ambient stalk. -/
noncomputable def supportComplementFunctionFieldAlgEquiv
    (I : X.IdealSheafData) [Nonempty I.supportComplement]
    (x : X) :
    letI : Algebra (X.presheaf.stalk x)
        (I.supportComplement : Scheme).functionField :=
      I.supportComplementFunctionFieldAlgebra x
    X.functionField ≃ₐ[X.presheaf.stalk x]
      (I.supportComplement : Scheme).functionField := by
  letI : Algebra (X.presheaf.stalk x)
      (I.supportComplement : Scheme).functionField :=
    I.supportComplementFunctionFieldAlgebra x
  exact AlgEquiv.ofRingEquiv
    (f := I.supportComplement.ι.functionFieldRingEquivOfIsOpenImmersion) (by
      intro a
      change
        I.supportComplement.ι.functionFieldRingEquivOfIsOpenImmersion
            (algebraMap (X.presheaf.stalk x) X.functionField a) =
          I.supportComplement.ι.functionFieldRingEquivOfIsOpenImmersion
            (algebraMap (X.presheaf.stalk x) X.functionField a)
      rfl)

/-- The complement function field is a fraction field of every ambient
stalk, through the canonical open-immersion map. -/
theorem supportComplementFunctionField_isFractionRing
    (I : X.IdealSheafData) [Nonempty I.supportComplement]
    (x : X) :
    letI : Algebra (X.presheaf.stalk x)
        (I.supportComplement : Scheme).functionField :=
      I.supportComplementFunctionFieldAlgebra x
    IsFractionRing (X.presheaf.stalk x)
      (I.supportComplement : Scheme).functionField := by
  let : Algebra (X.presheaf.stalk x)
      (I.supportComplement : Scheme).functionField :=
    I.supportComplementFunctionFieldAlgebra x
  exact IsFractionRing.of_algEquiv
    (I.supportComplementFunctionFieldAlgEquiv x)

end AlgebraicGeometry.Scheme.IdealSheafData

end
