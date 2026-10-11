/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualTameCoordinate
import EtaleFundamentalGroups.Inertia.ActualFiniteQuotientTameValueTower

/-!
# Compatibility over the actual tame-degree set

An arbitrary divisibility relation between actual tame degrees need not come
from an inclusion of the selected finite stages. A common upper finite
Galois stage proves the required power equation without such an assumption.
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

/-- The actual quotient-valued coordinates form a compatible family for
the literal restricted roots system. -/
theorem actualTameCoordinate_compatible :
    (actualFiniteTameRootsSystem A K L Q).CompatibleMaps
      (fun n => (actualTameCoordinate A K L Q n).toFun) := by
  intro m n hmn
  funext σ
  apply rootsOfUnity.coe_injective
  change (((actualTameCoordinate A K L Q n).toFun σ).val).val ^
      (n.val.val / m.val.val) =
    (((actualTameCoordinate A K L Q m).toFun σ).val).val
  rw [actualTameCoordinate_eval A K L Q m m.property.choose m.property.choose_spec σ,
    actualTameCoordinate_eval A K L Q n n.property.choose n.property.choose_spec σ]
  have hm : actualFiniteStageTameOrder A K L Q m.property.choose = m.val.val :=
    congrArg Subtype.val m.property.choose_spec
  have hn : actualFiniteStageTameOrder A K L Q n.property.choose = n.val.val :=
    congrArg Subtype.val n.property.choose_spec
  have hdiv : actualFiniteStageTameOrder A K L Q m.property.choose ∣
      actualFiniteStageTameOrder A K L Q n.property.choose := by
    rw [hm, hn]
    exact hmn
  have hvalue := actualFiniteQuotientTameValue_pow_of_dvd A K L Q
    m.property.choose n.property.choose hdiv σ
  rw [hm, hn] at hvalue
  exact hvalue

end EtaleFundamentalGroups.Inertia
