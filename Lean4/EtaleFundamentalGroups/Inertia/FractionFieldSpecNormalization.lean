/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteEtaleAwayNormalizationAction
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The actual function field over a fraction-field spectrum

The algebra defined by the structure morphism of `Spec K` agrees with the
composite of the two canonical fraction-field maps. This comparison is made
before installing the scalar tower, so the resulting fraction-ring structure
uses precisely the algebra of normalization geometry.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The actual function field of the spectrum of a fraction field is a
fraction field of the original ring for its geometric structure algebra. -/
theorem affineMorphismFunctionFieldAlgebra_isFractionRing
    (R K : Type u) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    let : Algebra R (Spec (.of K)).functionField :=
      affineMorphismFunctionFieldAlgebra R
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    IsFractionRing R (Spec (.of K)).functionField := by
  let F : Type u := (Spec (.of K)).functionField
  let : Algebra K F := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of K)
  rw [affineMorphismFunctionFieldAlgebra_specMap R K (algebraMap R K)]
  let : Algebra R F := ((algebraMap K F).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K F := IsScalarTower.of_algebraMap_eq' rfl
  let : IsFractionRing K F := AlgebraicGeometry.functionField_isFractionRing_of_affine (.of K)
  exact IsFractionRing.trans R K F

end EtaleFundamentalGroups.Inertia
