/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteIdealTameOrder
import EtaleFundamentalGroups.Inertia.UniformizerRadicalRamification
import ValuedFieldTheory.Ramification.HilbertRamification.RingTameOrderVanishing
import SchemeTheory.RingTheory.Ramification.StabilizerLocalizationAction
import Mathlib.Algebra.Algebra.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Tame orders and ramification indices

Proves that the finite tame order at the original normalization prime divides its ramification
index.
-/

noncomputable section

open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

open RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u v w

private theorem localizedCoefficient_ne_zero
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    (Q : Ideal B) [Q.IsPrime] (a : A) (ha : a ≠ 0) :
    algebraMap B (Localization.AtPrime Q) (algebraMap A B a) ≠ 0 := by
  have hB : algebraMap A B a ≠ 0 := fun h =>
    ha ((FaithfulSMul.algebraMap_injective A B) (h.trans (map_zero (algebraMap A B)).symm))
  exact mem_nonZeroDivisors_iff_ne_zero.mp
    (IsLocalization.nonZeroDivisors_le_comap Q.primeCompl (Localization.AtPrime Q)
      (mem_nonZeroDivisors_iff_ne_zero.mpr hB))

private theorem localizedCoefficient_fixed
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type w) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (Q : Ideal B) [Q.IsPrime] (a : A) (σ : MulAction.stabilizer G Q) :
    σ • algebraMap B (Localization.AtPrime Q) (algebraMap A B a) =
      algebraMap B (Localization.AtPrime Q) (algebraMap A B a) := by
  rw [SchemeTheory.stabilizerLocalization_smul_algebraMap, smul_algebraMap]

/-- The actual finite tame order at the original normalization prime divides
its original ramification index. The coefficient nonzero/fixed calculations,
length comparison and one-DVR character calculation remain separate scopes. -/
theorem finiteIdealTameOrder_dvd_ramificationIdx
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [FaithfulSMul A B]
    (G : Type w) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal A)] (hQ : Q ≠ ⊥) :
    finiteIdealTameOrder B G Q hQ ∣ Q.ramificationIdx A := by
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hQ (Localization.AtPrime Q)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  rw [ramificationIdx_eq_ord_localized_uniformizer Q π hπ]
  change tameOrder (Localization.AtPrime Q) (MulAction.stabilizer G Q) ∣ _
  exact tameOrder_dvd_ord_of_fixed (Localization.AtPrime Q) (MulAction.stabilizer G Q)
    (algebraMap B (Localization.AtPrime Q) (algebraMap A B π))
    (localizedCoefficient_ne_zero Q π hπ.ne_zero)
    (fun σ => localizedCoefficient_fixed G Q π σ)

end EtaleFundamentalGroups.Inertia

end
