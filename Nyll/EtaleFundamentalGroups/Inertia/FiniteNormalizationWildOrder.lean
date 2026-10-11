/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NativeFiniteNormalizationWildOrder
import Nyll.EtaleFundamentalGroups.Inertia.NativeFiniteNormalizationTameProperties
import Nyll.EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
import Nyll.EtaleFundamentalGroups.Inertia.FiniteLevelFieldAlgebra
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameOrder
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Residue-primary wild order at an actual finite stage

The native finite field supplies the already proved native normalization
order theorem directly. Its scalar environment stays inside that theorem;
no original prime or inertia group is opened in this adapter.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- Every nonzero prime of the actual finite normalization has primary wild order. -/
theorem finiteNormalizationWildOrder_exists_expChar_pow
    (A : Type u) [rA : CommRing A] [dedA : IsDedekindDomain A]
    (K : Type v) (L : Type w) [fK : Field K] [fL : Field L]
    [aAK : Algebra A K] [frAK : IsFractionRing A K]
    [aKL : Algebra K L] [aAL : Algebra A L] [tAKL : IsScalarTower A K L]
    [IsGalois K L] (E : FiniteGaloisIntermediateField K L) :
    let : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E).carrier :=
      finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
    ∀ (Q : Ideal (finiteAbsoluteNormalizationAlgebra A K L E).carrier)
      [Q.IsPrime] (hQ : Q ≠ ⊥),
      ∃ n : ℕ, commAlgIdealWildOrder A (finiteAbsoluteNormalizationAlgebra A K L E) Q hQ =
        (ringExpChar Q.ResidueField) ^ n := by
  exact nativeFiniteNormalizationWildOrder_exists_expChar_pow A K
    (finiteLevelFieldAlgebra A K L E)
    (Field.toIsField (finiteLevelFieldAlgebra A K L E).carrier)

end EtaleFundamentalGroups.Inertia

end
