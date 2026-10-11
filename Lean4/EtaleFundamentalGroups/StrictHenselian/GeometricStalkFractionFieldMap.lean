/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkNormalDomain
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Mathlib.RingTheory.Localization.FractionRing


/-!
# The actual strict generic field map over a normal local domain

The actual geometric stalk is a domain, and its local structure map is
faithfully flat and injective. Localizing this injection constructs the map
between the actual fraction fields and its compatibility with the original
structure map. Neither a DVR nor a generic tensor comparison is required.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsLocalRing R] [Field Ω] (φ : R →+* Ω) [IsLocalHom φ]

/-- The actual field map obtained from the actual geometric-stalk injection. -/
def geometricStalkFractionFieldMap :
    FractionRing R →+* FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
  IsFractionRing.map (geometricStalkStructureMap_injective φ)

/-- The induced fraction-field map extends the actual local structure map. -/
theorem geometricStalkFractionFieldMap_algebraMap (r : R) :
    geometricStalkFractionFieldMap φ (algebraMap R (FractionRing R) r) =
      algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))
        (geometricStalkStructureMap φ r) :=
  IsLocalization.map_eq
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
      (geometricStalkStructureMap φ) (geometricStalkStructureMap_injective φ)) r

end EtaleFundamentalGroups.StrictHenselian
