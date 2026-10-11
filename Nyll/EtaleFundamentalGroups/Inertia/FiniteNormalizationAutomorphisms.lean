/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import Nyll.EtaleFundamentalGroups.Inertia.FiniteLevelFieldAlgebra
import Nyll.EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
import Nyll.EtaleFundamentalGroups.Inertia.NativeFiniteNormalizationTameProperties

/-!
# Finiteness of finite normalization automorphisms

Proves finiteness of the intrinsic coefficient-automorphism group of a finite normalization.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v w

/-- Finiteness of the intrinsic coefficient automorphisms of an actual finite
normalization, proved before introducing any original prime or inertia. -/
theorem finiteAbsoluteNormalizationAutomorphisms_finite
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDedekindDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (E : FiniteGaloisIntermediateField K L) :
    Finite (finiteAbsoluteNormalizationAlgebra A K L E ≃ₐ[A]
      finiteAbsoluteNormalizationAlgebra A K L E) :=
  nativeNormalization_aut_finite A K (finiteLevelFieldAlgebra A K L E)
    (Field.toIsField (finiteLevelFieldAlgebra A K L E))

end EtaleFundamentalGroups.Inertia
