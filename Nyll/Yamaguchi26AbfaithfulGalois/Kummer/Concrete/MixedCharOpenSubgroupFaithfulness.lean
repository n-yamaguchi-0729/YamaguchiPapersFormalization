/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharFixingSubgroupFaithfulness
import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupConjugation
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotientAction
import Nyll.ProCGroups.FiniteGroups.PGroupFormation
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Complete mixed-characteristic faithfulness for open normal subgroups

Infinite Galois correspondence constructs the finite Galois fixed field of
an open normal subgroup. Its degree is the given index, so the established
field detection applies to the subgroup's actual pro-p residual quotient.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open ProCGroups ProCGroups.ProC

attribute [local instance] KummerTheory.fixingSubgroup_normal

/-- An open normal subgroup of any prime index has faithful quotient
conjugation on its abelianized pro-p residual quotient. -/
theorem mixedChar_openSubgroup_residualAbelianization_faithful
    {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [CharZero F]
    (vF : _root_.Valuation F (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vF]
    (p : ℕ) [Fact p.Prime]
    [hres : CharP (IsLocalRing.ResidueField vF.valuationSubring) p]
    (N : Subgroup Gal(Ω/F)) [N.Normal]
    (hN : IsOpen (N : Set Gal(Ω/F))) {r : ℕ} [Fact r.Prime]
    (hindex : N.index = r) :
    Function.Injective
      (residualAbelianizationQuotientConjugation
        (FiniteGroupClass.pGroup_fullFormation p) N (N.isClosed_of_isOpen hN)) := by
  let H : ClosedSubgroup Gal(Ω/F) := ⟨N, N.isClosed_of_isOpen hN⟩
  let S : IntermediateField F Ω := IntermediateField.fixedField N
  have hfix : S.fixingSubgroup = N := InfiniteGalois.fixingSubgroup_fixedField H
  have : FiniteDimensional F S := (InfiniteGalois.isOpen_iff_finite S).mp
    (by rw [hfix]; exact hN)
  have hcard : Nat.card (Gal(Ω/F) ⧸ N) = r := N.index_eq_card.symm.trans hindex
  have hdegree : Module.finrank F S = r :=
    (IsGalois.card_aut_eq_finrank F S).symm.trans
      ((Nat.card_congr (InfiniteGalois.normalAutEquivQuotient H).toEquiv).symm.trans hcard)
  have hfaith := mixedChar_fixingSubgroup_residualAbelianization_faithful S vF p hdegree
  let P : Subgroup Gal(Ω/F) → Prop := fun U =>
    ∀ hU : U.Normal, letI : U.Normal := hU
      ∀ hclosed : IsClosed (U : Set Gal(Ω/F)),
        Function.Injective (residualAbelianizationQuotientConjugation
          (FiniteGroupClass.pGroup_fullFormation p) U hclosed)
  have hP : P S.fixingSubgroup := fun _ _ => hfaith
  have hPN : P N := hfix ▸ hP
  exact hPN inferInstance (N.isClosed_of_isOpen hN)

end ClassFieldTower.Martinet.Shafarevich
