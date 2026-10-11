/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.FieldCoverQuotient

/-!
# Base-point transport for finite Galois field covers

This file expresses the canonical point of a field cover at a literal
composite geometric point and transports its pointed quotient.
-/

noncomputable section


open CategoryTheory AlgebraicGeometry
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups

universe u

variable (K L Omega F : Type u)
variable [Field K] [Field L] [Field Omega] [Field F]
variable [Algebra K L] [FiniteDimensional K L] [_root_.IsGalois K L]
variable [Algebra K Omega] [Algebra L Omega] [IsScalarTower K L Omega]
variable [IsSepClosed Omega]
variable [Algebra K F] [Algebra F Omega] [IsScalarTower K F Omega]

/-- The canonical field-cover point expressed at the literal composite
geometric point `Spec Omega → Spec F → Spec K`. -/
noncomputable def fieldFiniteEtaleCoverCompositePoint :
    (fiber (ξ F Omega ≫ ξ K F)).obj (FiniteEtale.mk (ξ K L)) :=
  (fieldBasePointFiberIso K F Omega).inv.app (FiniteEtale.mk (ξ K L))
    (fieldFiniteEtaleCoverCanonicalPoint K L Omega)

end EtaleFundamentalGroups

end
