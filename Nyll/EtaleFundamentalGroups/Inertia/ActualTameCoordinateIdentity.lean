/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualTameCoordinate

/-!
# Identity detection at one actual tame degree

The SAME canonical quotient-root equivalence preserves and reflects identity.
This comparison is proved before the global inverse-limit group is introduced.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] Ideal.Quotient.field

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- Evaluation at the degree of any finite stage recovers its canonical
coordinate, through the SAME canonical quotient comparison. -/
theorem actualTameCoordinate_at_stage
    (E : FiniteGaloisIntermediateField K L)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    (actualTameCoordinate A K L Q
        ⟨actualFiniteStageTameIndex A K L Q E, E, rfl⟩).toFun σ =
      (normalizationQuotientRootsEquiv A L Q
        (actualFiniteStageTameOrder A K L Q E)).toFun
        ((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ) := by
  apply rootsOfUnity.coe_injective
  exact (actualTameCoordinate_eval A K L Q
    ⟨actualFiniteStageTameIndex A K L Q E, E, rfl⟩ E rfl σ).trans
      (actualFiniteQuotientTameValue_eq_residue A K L Q E σ)

/-- At an actual degree, the canonical quotient coordinate is the identity
exactly when the SAME original finite coordinate is the identity. -/
theorem actualTameCoordinate_eq_one_iff
    (n : Subtype (actualFiniteTameDegreeSet A K L Q))
    (E : FiniteGaloisIntermediateField K L)
    (hE : actualFiniteStageTameIndex A K L Q E = n.val)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    (actualTameCoordinate A K L Q n).toFun σ = 1 ↔
      (actualFiniteTameCoordinate A K L Q E).hom'.toFun σ = 1 := by
  have hn : n = ⟨actualFiniteStageTameIndex A K L Q E, E, rfl⟩ :=
    Subtype.ext hE.symm
  rw [hn, actualTameCoordinate_at_stage A K L Q E σ]
  constructor
  · intro h
    apply (normalizationQuotientRootsEquiv A L Q
      (actualFiniteStageTameOrder A K L Q E)).toEquiv.injective
    exact h.trans (normalizationQuotientRootsEquiv A L Q
      (actualFiniteStageTameOrder A K L Q E)).toMonoidHom.map_one'.symm
  · intro h
    rw [h]
    exact (normalizationQuotientRootsEquiv A L Q
      (actualFiniteStageTameOrder A K L Q E)).toMonoidHom.map_one'

end EtaleFundamentalGroups.Inertia
