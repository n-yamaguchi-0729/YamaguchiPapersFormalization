/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.FiniteLevelFieldAlgebra
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Dedekind structure of finite normalizations

Proves that the native normalization at a finite Galois level is a Dedekind domain under the
original base-ring hypotheses.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v w

/-- The native actual finite normalization is Dedekind. The finite field's
inherited structures are supplied before this original-data proof. -/
theorem finiteAbsoluteNormalizationAlgebra_isDedekindDomain
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDedekindDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (E : FiniteGaloisIntermediateField K L) :
    IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E) := by
  exact integralClosure.isDedekindDomain A K (finiteLevelFieldAlgebra A K L E)

end EtaleFundamentalGroups.Inertia
