/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.Concrete.ResidueZeroInertiaDetection
import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.Concrete.ResidueZeroUnramifiedFaithfulness
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianResidueRestriction
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Henselian
import Nyll.ValuedFieldTheory.Valuation.FiniteResidueExtension
import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupAbsoluteAction
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.PrimeOrderTest

/-!
# Prime-index faithfulness in residue characteristic zero

For a residue-zero Henselian discrete valuation, ab-faithfulness of the
residue Galois group and finite primary root groups imply faithfulness of
the conjugation action associated with a prime-index open normal subgroup.
-/

namespace Yamaguchi26AbfaithfulGalois

open KummerTheory ValuationTheory.DiscreteValuationField
open ProCGroups.Abelian ProCGroups.FiniteStepSolvableQuotients
open RamificationTheory.HilbertRamification.ValuationSubring

attribute [local instance] KummerTheory.fixingSubgroup_normal

universe u v

/-- The prime-index quotient action is faithful over a residue-zero Henselian
DVF whenever the residue group is ab-faithful and its finite extensions have
finite primary root groups. -/
theorem residueZero_openNormal_prime_index_faithful
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [CharZero K]
    (D : HenselianDVF.{u, v} K) [CharZero D.residueField]
    (hres : IsAbFaithful Gal(AlgebraicClosure D.residueField/D.residueField))
    (hroots : ∀ (E : Type u) [Field E] [Algebra D.residueField E]
      [FiniteDimensional D.residueField E] (p : ℕ), p.Prime →
      Finite (CommGroup.primaryComponent Eˣ p))
    (N : OpenNormalSubgroup Gal(Ω/K))
    (hprime : (N : Subgroup Gal(Ω/K)).index.Prime) :
    Function.Injective (quotientConjugationTopologicalAbelianizationMap
      (N : Subgroup Gal(Ω/K))) := by
  classical
  let H : ClosedSubgroup Gal(Ω/K) := ⟨N.toSubgroup, N.isClosed⟩
  let L : IntermediateField K Ω := IntermediateField.fixedField (N : Subgroup Gal(Ω/K))
  have hfix : L.fixingSubgroup = (N : Subgroup Gal(Ω/K)) :=
    InfiniteGalois.fixingSubgroup_fixedField H
  have : FiniteDimensional K L := (InfiniteGalois.isOpen_iff_finite L).mp
    (by rw [hfix]; exact N.isOpen)
  have hdeg : Module.finrank K L = (N : Subgroup Gal(Ω/K)).index :=
    (IsGalois.card_aut_eq_finrank K L).symm.trans
      ((Nat.card_congr (InfiniteGalois.normalAutEquivQuotient H).toEquiv).symm.trans
        (N : Subgroup Gal(Ω/K)).index_eq_card.symm)
  let F : HenselianDVF L := FiniteExtensionLocalization.henselianDVF D
  have : D.valuation.HasExtension F.valuation :=
    FiniteExtensionLocalization.henselianDVF_hasExtension D
  have : CharZero F.residueField :=
    charZero_of_injective_algebraMap (algebraMap D.residueField F.residueField).injective
  obtain ⟨Γ, hΓ, w, hw⟩ :=
    Valuation.chevalley_hasSomeExtensionTo (L := Ω) F.valuation
  let : LinearOrderedCommGroupWithZero Γ := hΓ
  have : F.valuation.HasExtension w := hw
  have : D.valuation.HasExtension w :=
    Valuation.hasExtension_trans D.valuation F.valuation w
  by_cases hI : (henselianResidueAction D.valuation w).ker ≤
      (N : Subgroup Gal(Ω/K))
  · exact residueZero_openNormal_faithful_of_inertia_le D w hres N hI
  · obtain ⟨σ, hσ, hσN⟩ := Set.not_subset.mp hI
    have hσres : henselianResidueAction D.valuation w σ = 1 := hσ
    have hτres := henselianResidueAction_restrictNormal_eq_one
      D.valuation F.valuation w σ hσres
    let τ : inertiaGroup K F.valuation.valuationSubring :=
      ⟨henselianGalToDecomposition D.valuation F.valuation (σ.restrictNormal L),
        congrArg AlgEquiv.toRingEquiv hτres⟩
    have hτ : τ ≠ 1 := by
      intro heq
      apply hσN
      rw [← hfix, ← L.restrictNormalHom_ker]
      exact congrArg (fun z : inertiaGroup K F.valuation.valuationSubring =>
        ((z : decompositionGroup K F.valuation.valuationSubring) : Gal(L/K))) heq
    have : FiniteDimensional D.residueField F.residueField :=
      _root_.Valuation.finiteDimensional_residueField D.valuation F.valuation
    have : Finite (CommGroup.primaryComponent F.residueFieldˣ
        (N : Subgroup Gal(Ω/K)).index) := hroots F.residueField _ hprime
    have hact := residueZero_inertia_abelianization_action_ne_one F hprime hdeg τ hτ
    have hquot := fixingSubgroup_quotient_action_ne_one_of_absolute_action_ne_one L σ hact
    have hfaith : Function.Injective
        (quotientConjugationTopologicalAbelianizationMap L.fixingSubgroup) := by
      apply (injective_iff_ne_one_of_prime_card _ ?_).mpr
      · intro h
        apply hquot
        rw [h]
        rfl
      · rw [← L.fixingSubgroup.index_eq_card, hfix]
        exact hprime
    let P : Subgroup Gal(Ω/K) → Prop := fun U =>
      ∀ hU : U.Normal, letI : U.Normal := hU
        Function.Injective (quotientConjugationTopologicalAbelianizationMap U)
    have hP : P L.fixingSubgroup := fun _ => hfaith
    exact (hfix ▸ hP) inferInstance

end Yamaguchi26AbfaithfulGalois
