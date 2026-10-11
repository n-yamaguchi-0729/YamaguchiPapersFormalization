/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.FiniteNormalizationWildOrder
import Nyll.EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import Nyll.EtaleFundamentalGroups.Inertia.FiniteLevelNormalizationAlgebra
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationResidueCharacteristic
import Nyll.SchemeTheory.Normalization.NativeNormalizationPrime
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage

/-!
# Primary wild order over the original residue characteristic

Literal prime contraction identifies the finite prime residue characteristic
with the original base residue characteristic. No subgroup or inertia group
is introduced during this arithmetic step.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- The existing actual finite wild order is a power of the base residue
exponential characteristic, supplied from the same actual normalization. -/
theorem actualFiniteStageWildOrder_exists_baseResidue_expChar_pow
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L) :
    ∃ n : ℕ, actualFiniteStageWildOrder A K L Q E =
      (ringExpChar (IsLocalRing.ResidueField A)) ^ n := by
  have dB : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E).carrier :=
    finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  have qPrime : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
    finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  have qOver : (finiteAbsoluteNormalizationPrime A K L Q E).LiesOver
      (IsLocalRing.maximalIdeal A) :=
    subalgebraNormalizationPrime_liesOver_maximalIdeal
      (finiteLevelNormalizationSubalgebra A K L E) Q
  obtain ⟨n, hn⟩ := finiteNormalizationWildOrder_exists_expChar_pow A K L E
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)
  refine ⟨n, hn.trans ?_⟩
  exact congrArg (fun p : ℕ => p ^ n)
    (idealResidue_ringExpChar_eq_baseResidue A
      (finiteAbsoluteNormalizationAlgebra A K L E).carrier
      (finiteAbsoluteNormalizationPrime A K L Q E))

end EtaleFundamentalGroups.Inertia

end
