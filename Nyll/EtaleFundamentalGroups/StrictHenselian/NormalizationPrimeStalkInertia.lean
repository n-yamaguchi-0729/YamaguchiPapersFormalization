/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaCompact
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeEmbedding
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeStalkFixedField
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeStalkFraction
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Original inertia is the group fixing the actual stalk fraction image

The proved comparison identifies the range of the actual constructed
fraction-field embedding. Closedness of the same original inertia subgroup
and the pinned infinite Galois correspondence then identify its fixing
group with inertia. The actual embedded field is retained throughout.
-/

noncomputable section

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia

universe u v

attribute [local instance] normalizationInertiaImageAction

variable (A : Type u) (K : Type v) (L : Type u)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
    (Q : Ideal (integralClosure A L)) [Q.IsMaximal]

/-- The subgroup fixing the range of the actual embedded geometric-stalk
fraction field is the same original normalization inertia subgroup. -/
theorem geometricStalkFractionToNormalizationField_fixingSubgroup :
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    fixingSubgroup Gal(L/K)
        ((geometricStalkFractionToNormalizationField A L Q).range : Set L) =
      Q.inertia Gal(L/K) := by
  intro actualAlgebraic actualFaithful actualHenselian actualSepClosed
  rw [geometricStalkFractionToNormalizationField_range_eq_fixedField A K L Q]
  exact InfiniteGalois.fixingSubgroup_fixedField
    (⟨Q.inertia Gal(L/K), actualNormalizationInertia_isClosed A K L Q⟩ :
      ClosedSubgroup Gal(L/K))

/-- An original ambient Galois automorphism fixes the actual stalk-fraction
embedding precisely when it belongs to the original normalization inertia. -/
theorem geometricStalkFractionToNormalizationField_comp_eq_self_iff
    (σ : Gal(L/K)) :
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    σ.toRingHom.comp (geometricStalkFractionToNormalizationField A L Q) =
        geometricStalkFractionToNormalizationField A L Q ↔
      σ ∈ Q.inertia Gal(L/K) := by
  intro actualAlgebraic actualFaithful actualHenselian actualSepClosed
  rw [← geometricStalkFractionToNormalizationField_fixingSubgroup A K L Q]
  constructor
  · intro h
    apply (mem_fixingSubgroup_iff Gal(L/K)).mpr
    intro x hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    exact RingHom.congr_fun h y
  · intro h
    apply RingHom.ext
    intro y
    exact (mem_fixingSubgroup_iff Gal(L/K)).mp h
      ((geometricStalkFractionToNormalizationField A L Q) y) ⟨y, rfl⟩

end EtaleFundamentalGroups.StrictHenselian
