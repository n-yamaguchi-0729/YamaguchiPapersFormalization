/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
import Nyll.EtaleFundamentalGroups.Inertia.NativeFiniteNormalizationTameProperties

/-!
# Tame orders of finite normalizations

Proves positivity of finite-normalization tame orders and their invertibility in the original
local coefficient ring.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDedekindDomain A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (E : FiniteGaloisIntermediateField K L)

/-- Positivity for all actual finite-normalization primes, before an upper
normalization prime is brought into the scope. -/
theorem finiteNormalizationTameOrder_pos
    (q : Ideal (finiteAbsoluteNormalizationAlgebra A K L E)) [q.IsPrime] (hq : q ≠ ⊥) :
    let : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E) :=
      finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
    0 < commAlgIdealTameOrder A (finiteAbsoluteNormalizationAlgebra A K L E) q hq :=
  by
    let q' : Ideal (SchemeTheory.normalizationCommAlgCat A (finiteLevelFieldAlgebra A K L E)) := q
    have : q'.IsPrime := ‹q.IsPrime›
    exact nativeFiniteNormalizationTameOrder_pos A K (finiteLevelFieldAlgebra A K L E)
      (Field.toIsField (finiteLevelFieldAlgebra A K L E)) q' hq

/-- The same original finite stages have tame order invertible in the
original local coefficient ring, with no residue-separability hypothesis. -/
theorem finiteNormalizationTameOrder_isUnit [IsLocalRing A]
    (q : Ideal (finiteAbsoluteNormalizationAlgebra A K L E)) [q.IsPrime] (hq : q ≠ ⊥) :
    let : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E) :=
      finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
    IsUnit (commAlgIdealTameOrder A (finiteAbsoluteNormalizationAlgebra A K L E) q hq : A) :=
  by
    let q' : Ideal (SchemeTheory.normalizationCommAlgCat A (finiteLevelFieldAlgebra A K L E)) := q
    have : q'.IsPrime := ‹q.IsPrime›
    exact nativeFiniteNormalizationTameOrder_isUnit A K (finiteLevelFieldAlgebra A K L E)
      (Field.toIsField (finiteLevelFieldAlgebra A K L E)) q' hq

end EtaleFundamentalGroups.Inertia
