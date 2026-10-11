/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationInertiaConjugate
import EtaleFundamentalGroups.Inertia.NativeIdealInertiaInclusion
import Mathlib.Algebra.Group.Subgroup.Map

/-!
# The actual original inertia inside decomposition

The two original action names use the identical normalization action value.
The inclusion is the standard inclusion supplied by ideal inertia stability.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] normalizationCommAlgGaloisAction

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier)

/-- The actual inertia includes into the SAME original decomposition group. -/
noncomputable def actualNormalizationInertiaToDecomposition :
    (actualNormalizationInertiaGroup A K L Q).carrier →*
      (normalizationDecompositionGroup A K L Q).carrier :=
  nativeIdealInertiaToStabilizer (normalizationCommAlgCat A L).carrier Gal(L/K) Q

/-- The inclusion identifies original inertia conjugation with conjugation in D. -/
theorem actualNormalizationInertiaToDecomposition_conjugate
    (d : (normalizationDecompositionGroup A K L Q).carrier)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    (actualNormalizationInertiaToDecomposition A K L Q).toFun
        (originalFiniteNormalizationInertiaConjugate A K L Q d σ) =
      d * (actualNormalizationInertiaToDecomposition A K L Q).toFun σ * d⁻¹ :=
  nativeIdealInertiaToStabilizer_conjugate (normalizationCommAlgCat A L).carrier
    Gal(L/K) Q d σ

end EtaleFundamentalGroups.Inertia
