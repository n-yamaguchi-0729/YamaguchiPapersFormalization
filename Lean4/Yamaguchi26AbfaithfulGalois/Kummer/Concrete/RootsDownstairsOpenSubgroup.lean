/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.Kummer.Concrete.RootsDownstairsFixedSubgroup
import ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Roots downstairs for arbitrary open normal subgroups

Infinite Galois correspondence supplies the finite Galois fixed field of an
open normal subgroup. Prime quotient order supplies its prime field degree,
so roots-downstairs detection applies to the original quotient action.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open ProCGroups.Abelian

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [CharZero K]
  [IsAlgClosure K Ω]

/-- An open normal subgroup of prime index has faithful quotient conjugation
when its fixed field satisfies the original roots-downstairs conditions. -/
theorem rootsDownstairs_openSubgroup_quotient_action_faithful
    (N : OpenSubgroup Gal(Ω/K)) [N.toSubgroup.Normal]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card (Gal(Ω/K) ⧸ N.toSubgroup) = p)
    (hμ : (primitiveRoots p K).Nonempty)
    (hfinite : Set.Finite {ξ : IntermediateField.fixedField N.toSubgroup |
      ∃ m : ℕ, ξ ^ (p ^ m) = 1})
    (hdown : ∀ ξ : IntermediateField.fixedField N.toSubgroup,
      (∃ m : ℕ, ξ ^ (p ^ m) = 1) →
        ξ ∈ Set.range (algebraMap K (IntermediateField.fixedField N.toSubgroup))) :
    Function.Injective (quotientConjugationTopologicalAbelianizationMap N.toSubgroup) := by
  let H : ClosedSubgroup Gal(Ω/K) := ⟨N.toSubgroup, N.isClosed⟩
  have hfix : (IntermediateField.fixedField N.toSubgroup).fixingSubgroup = N.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField H
  have : FiniteDimensional K (IntermediateField.fixedField N.toSubgroup) :=
    (InfiniteGalois.isOpen_iff_finite (IntermediateField.fixedField N.toSubgroup)).mp
      (by rw [hfix]; exact N.isOpen)
  have hdeg : Module.finrank K (IntermediateField.fixedField N.toSubgroup) = p :=
    (IsGalois.card_aut_eq_finrank K (IntermediateField.fixedField N.toSubgroup)).symm.trans
      ((Nat.card_congr (InfiniteGalois.normalAutEquivQuotient H).toEquiv).symm.trans hcard)
  have hfaith := rootsDownstairs_fixedSubgroup_quotient_action_faithful
    (IntermediateField.fixedField N.toSubgroup) hp hdeg hμ hfinite hdown
  let P : Subgroup Gal(Ω/K) → Prop := fun U =>
    ∀ hU : U.Normal, letI : U.Normal := hU
      Function.Injective (quotientConjugationTopologicalAbelianizationMap U)
  have hP : P (IntermediateField.fixedField N.toSubgroup).fixingSubgroup := fun _ => hfaith
  have hPN : P N.toSubgroup := hfix ▸ hP
  exact hPN inferInstance

end ClassFieldTower.Martinet.Shafarevich
