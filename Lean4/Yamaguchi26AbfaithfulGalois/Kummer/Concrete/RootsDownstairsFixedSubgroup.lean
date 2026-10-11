/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.Kummer.Concrete.RootsDownstairsAction
import GaloisCohomology.Kummer.Concrete.FixedSubgroupAbsoluteAction
import GaloisCohomology.Kummer.Concrete.FixedSubgroupConjugation
import ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Roots downstairs detect actual quotient conjugation

Inside any algebraic closure, the quotient by the fixing subgroup of a
prime-degree Galois intermediate field acts faithfully on that subgroup's
topological abelianization under the roots-downstairs hypotheses.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory ProCGroups.Abelian

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [CharZero K]
  [IsAlgClosure K Ω] (L : IntermediateField K Ω)
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] fixingSubgroup_normal

/-- The actual quotient group acts faithfully on the abelianization of the
open normal fixing subgroup under the original roots-downstairs conditions. -/
theorem rootsDownstairs_fixedSubgroup_quotient_action_faithful
    {p : ℕ} (hp : p.Prime) (hdeg : Module.finrank K L = p)
    (hμ : (primitiveRoots p K).Nonempty)
    (hfinite : Set.Finite {ξ : L | ∃ m : ℕ, ξ ^ (p ^ m) = 1})
    (hdown : ∀ ξ : L, (∃ m : ℕ, ξ ^ (p ^ m) = 1) →
      ξ ∈ Set.range (algebraMap K L)) :
    Function.Injective
      (quotientConjugationTopologicalAbelianizationMap L.fixingSubgroup) := by
  apply (injective_iff_map_eq_one
    (quotientConjugationTopologicalAbelianizationMap L.fixingSubgroup)).mpr
  intro q hq
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective q
  apply (QuotientGroup.eq_one_iff (N := L.fixingSubgroup) σ).mpr
  by_contra hσ
  have hrestrict : σ.restrictNormal L ≠ 1 := by
    intro heq
    apply hσ
    rw [← L.restrictNormalHom_ker]
    exact heq
  have hdetect := rootsDownstairs_abelianization_action_ne_one
    hp hdeg hμ hfinite hdown (σ.restrictNormal L) hrestrict
  exact fixingSubgroup_quotient_action_ne_one_of_absolute_action_ne_one L σ hdetect hq

end ClassFieldTower.Martinet.Shafarevich
