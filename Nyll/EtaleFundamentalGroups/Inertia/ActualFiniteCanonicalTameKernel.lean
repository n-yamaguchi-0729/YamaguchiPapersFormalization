/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteCanonicalTameMorphism
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteWildSubgroup
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgCanonicalTameCoprimeExactness
import Nyll.EtaleFundamentalGroups.Inertia.FiniteNormalizationAutomorphisms
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameOrderTower
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameIndex
import Nyll.EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage

/-!
# The actual normalized finite character has the actual wild kernel

The already proved actual finite arithmetic supplies coprimality of n and
e/n. The native coefficient theorem proves that this actual normalization
preserves the independent principal-unit kernel.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- The SAME e/n-normalized canonical character has the independently
constructed principal-unit subgroup as kernel. -/
theorem actualFiniteCanonicalTameMorphism_ker (E : FiniteGaloisIntermediateField K L) :
    (actualFiniteCanonicalTameMorphism A K L Q E).hom'.ker =
      actualFiniteWildSubgroup A K L Q E := by
  have dB : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E).carrier :=
    finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  have qPrime : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
    finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  have fG : Finite ((finiteAbsoluteNormalizationAlgebra A K L E).carrier ≃ₐ[A]
      (finiteAbsoluteNormalizationAlgebra A K L E).carrier) :=
    finiteAbsoluteNormalizationAutomorphisms_finite A K L E
  have hcop : Nat.Coprime (actualFiniteStageTameOrder A K L Q E)
      ((finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A /
        actualFiniteStageTameOrder A K L Q E) :=
    (actualFiniteStage_tame_arithmetic A K L Q E).2
      (actualFiniteStageTameOrder A K L Q E)
      (actualFiniteStageTameOrder_isUnit A K L Q E)
  exact (commAlgCanonicalTameMorphism_exact_of_coprime A
    (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E) hcop).2

end EtaleFundamentalGroups.Inertia
