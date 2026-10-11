/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteLevelNormalizationAlgebra
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure

/-!
# Finite intermediate fields as coefficient algebras

Bundles a finite Galois intermediate field as a coefficient algebra and supplies its inherited
field, scalar-tower, finite-dimensional, and Galois structures.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

/-- The actual finite field, retaining its inherited native coefficient algebra. -/
def finiteLevelFieldAlgebra (E : FiniteGaloisIntermediateField K L) : CommAlgCat.{w} A :=
  subalgebraCommAlgCat (finiteLevelNormalizationSubalgebra A K L E)

/-- Its field structure is the original finite intermediate field structure. -/
instance finiteLevelFieldAlgebra_field (E : FiniteGaloisIntermediateField K L) :
    Field (finiteLevelFieldAlgebra A K L E).carrier :=
  inferInstanceAs (Field E)

/-- Its K-action is the original intermediate-field action. -/
instance finiteLevelFieldAlgebra_algebra (E : FiniteGaloisIntermediateField K L) :
    Algebra K (finiteLevelFieldAlgebra A K L E).carrier :=
  inferInstanceAs (Algebra K E)

instance finiteLevelFieldAlgebra_tower (E : FiniteGaloisIntermediateField K L) :
    IsScalarTower A K (finiteLevelFieldAlgebra A K L E).carrier :=
  inferInstanceAs (IsScalarTower A K E)

instance finiteLevelFieldAlgebra_finiteDimensional (E : FiniteGaloisIntermediateField K L) :
    FiniteDimensional K (finiteLevelFieldAlgebra A K L E).carrier :=
  inferInstanceAs (FiniteDimensional K E)

instance finiteLevelFieldAlgebra_isGalois (E : FiniteGaloisIntermediateField K L) :
    IsGalois K (finiteLevelFieldAlgebra A K L E).carrier :=
  inferInstanceAs (IsGalois K E)

end EtaleFundamentalGroups.Inertia

end
