/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
import EtaleFundamentalGroups.Inertia.CommAlgIdealTameOrder
import SchemeTheory.Normalization.NativeNormalizationPrime
import Mathlib.Algebra.Algebra.Basic

/-!
# Tame and wild degrees at finite stages

Proves nonvanishing of the finite contracted normalization prime and defines the tame and wild
orders for its intrinsic coefficient-automorphism action.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]

omit [IsGalois K L] in
/-- The literal contracted prime of the actual finite normalization is
nonzero, derived from the original DVR and the original maximal prime. -/
theorem finiteAbsoluteNormalizationPrime_ne_bot
    (E : FiniteGaloisIntermediateField K L) :
    finiteAbsoluteNormalizationPrime A K L Q E ≠ ⊥ := by
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  exact subalgebraNormalizationPrime_ne_bot
    (finiteLevelNormalizationSubalgebra A K L E) Q

/-- The actual tame degree of a finite Galois subextension at the chosen
original normalization prime. All local rings, actions and kernels are
constructed from these original data. -/
def actualFiniteStageTameOrder (E : FiniteGaloisIntermediateField K L) : ℕ := by
  letI := finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  exact commAlgIdealTameOrder A (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)

/-- The actual wild degree of the same finite stage and the same intrinsic
coefficient-automorphism action. -/
def actualFiniteStageWildOrder (E : FiniteGaloisIntermediateField K L) : ℕ := by
  letI := finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  exact commAlgIdealWildOrder A (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)

end EtaleFundamentalGroups.Inertia

end
