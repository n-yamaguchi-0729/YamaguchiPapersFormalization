/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharFixingSubgroupDetection
import GaloisCohomology.Kummer.Concrete.FixedSubgroupConjugation
import ProCGroups.ProC.MaximalQuotients.ResidualQuotientAction
import ProCGroups.FiniteGroups.PGroupFormation
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Perfect

/-!
# Faithful quotient action on the actual pro-p abelianization

Over a complete mixed-characteristic discretely valued base, the quotient
by a prime-degree fixing subgroup acts faithfully on the topological
abelianization of that subgroup's intrinsic pro-p residual quotient.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open ProCGroups ProCGroups.ProC

attribute [local instance] KummerTheory.fixingSubgroup_normal

/-- The actual prime-degree Galois quotient acts faithfully on the
abelianization of the fixing subgroup's canonical pro-p residual quotient. -/
theorem mixedChar_fixingSubgroup_residualAbelianization_faithful
    {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [CharZero F]
    (S : IntermediateField F Ω) [IsGalois F S]
    (vF : _root_.Valuation F (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vF]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField vF.valuationSubring) p]
    {r : ℕ} [Fact r.Prime] (hdegree : Module.finrank F S = r) :
    Function.Injective
      (residualAbelianizationQuotientConjugation
        (FiniteGroupClass.pGroup_fullFormation p) S.fixingSubgroup
        (InfiniteGalois.fixingSubgroup_isClosed S)) := by
  apply (residualAbelianizationQuotientConjugation_injective_iff
    (FiniteGroupClass.pGroup_fullFormation p) S.fixingSubgroup
    (InfiniteGalois.fixingSubgroup_isClosed S)).mpr
  intro g hg
  exact mixedChar_fixingSubgroup_residualAbelianization_conjugation_ne_one
    S vF p hdegree g hg

end ClassFieldTower.Martinet.Shafarevich
