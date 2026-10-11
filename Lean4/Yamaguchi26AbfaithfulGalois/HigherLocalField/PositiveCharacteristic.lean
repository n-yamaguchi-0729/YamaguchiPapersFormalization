/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.HigherLocalField.Basic
import Yamaguchi26AbfaithfulGalois.Kummer.PositiveCharacteristicCompleteDetection
import Yamaguchi26AbfaithfulGalois.Kummer.PositiveCharacteristicPrimeDegreeReduction
import Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaOrdinary
import Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaEquivalence
import ValuedFieldTheory.Valuation.Completion.SeparableClosureAutTopology

/-!
# Positive-characteristic ab-faithfulness of higher local fields

Finite extensions inherit the higher local field structure. On every open
Galois layer, prime-degree detection follows from Artin--Schreier classes over
the complete discrete valuation at the first level. No embedding-problem
solvability result is used.
-/

namespace Yamaguchi26AbfaithfulGalois

open KummerTheory ProCGroups ProCGroups.ProC ProCGroups.Abelian
open ProCGroups.FiniteStepSolvableQuotients

universe u v

attribute [local instance] KummerTheory.fixingSubgroup_normal

private theorem higherLocal_openLayer_residual_faithful
    (n : ℕ) {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hK : ValuationTheory.IsHigherLocalField.{u, v} n K) (hn : 0 < n)
    (H : OpenSubgroup Gal(Ω/K))
    [CompactSpace (H : Subgroup Gal(Ω/K))]
    (N : OpenNormalSubgroup (H : Subgroup Gal(Ω/K)))
    (hprime : (N : Subgroup (H : Subgroup Gal(Ω/K))).index.Prime) :
    Function.Injective (residualAbelianizationQuotientConjugation
      (FiniteGroupClass.sigmaGroup_fullFormation {p})
      (N : Subgroup (H : Subgroup Gal(Ω/K))) N.isClosed) := by
  cases n with
  | zero => exact (Nat.not_lt_zero 0 hn).elim
  | succ n =>
      let F : IntermediateField K Ω := IntermediateField.fixedField (H : Subgroup Gal(Ω/K))
      let closedH : ClosedSubgroup Gal(Ω/K) := ⟨H.toSubgroup, H.isClosed⟩
      have hfix : F.fixingSubgroup = (H : Subgroup Gal(Ω/K)) :=
        InfiniteGalois.fixingSubgroup_fixedField closedH
      have : FiniteDimensional K F := (InfiniteGalois.isOpen_iff_finite F).mp (by
        rw [hfix]
        exact H.isOpen)
      have : IsSepClosure F Ω :=
        ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K F Ω⟩
      have : T2Space Gal(Ω/F) := krullTopology_t2 (K := F) (L := Ω)
      have : CharP F p := (Algebra.charP_iff K F p).mp inferInstance
      have hF : ValuationTheory.IsHigherLocalField.{u, v} (n + 1) F :=
        ValuationTheory.IsHigherLocalField.of_finiteExtension (n + 1) K F hK
      obtain ⟨D, _hD⟩ := hF
      let e₀ : (H : Subgroup Gal(Ω/K)) ≃ₜ* F.fixingSubgroup :=
        { toMulEquiv := MulEquiv.subgroupCongr hfix.symm
          continuous_toFun := Continuous.subtype_mk continuous_subtype_val
            (fun x => hfix.symm ▸ x.property)
          continuous_invFun := Continuous.subtype_mk continuous_subtype_val
            (fun x => hfix ▸ x.property) }
      let e : (H : Subgroup Gal(Ω/K)) ≃ₜ* Gal(Ω/F) := e₀.trans (fixingSubgroupContinuousEquiv F)
      let M : Subgroup Gal(Ω/F) :=
        (N : Subgroup (H : Subgroup Gal(Ω/K))).map e.toMulEquiv.toMonoidHom
      have : M.Normal :=
        (inferInstance : (N : Subgroup (H : Subgroup Gal(Ω/K))).Normal).map
          e.toMulEquiv.toMonoidHom e.surjective
      have hM : IsOpen (M : Set Gal(Ω/F)) := e.toHomeomorph.isOpenMap N N.isOpen
      let r : ℕ := (N : Subgroup (H : Subgroup Gal(Ω/K))).index
      have : Fact r.Prime := ⟨hprime⟩
      have hindex : M.index = r :=
        (N : Subgroup (H : Subgroup Gal(Ω/K))).index_map_equiv e.toMulEquiv
      have hfaith := primeDegree_separable_openSubgroup_residualAbelianization_faithful p
        (fun S _ hdeg => by
          obtain ⟨τ, _, z, hz⟩ := prime_order_detection_of_complete_charP p r D hdeg
          exact ⟨τ, z, hz⟩) M hM hindex
      have hNfaith := (residualAbelianizationQuotientConjugation_injective_map_iff
        (FiniteGroupClass.sigmaGroup_fullFormation {p}) e
        (N : Subgroup (H : Subgroup Gal(Ω/K))) N.isClosed).mp hfaith
      exact hNfaith

/-- Every positive-dimensional higher local field of positive characteristic is
ab-faithful. The proof detects every prime-order residual action directly. -/
theorem higher_local_field_abFaithful_of_charP
    (n : ℕ) (K : Type u) [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hK : ValuationTheory.IsHigherLocalField.{u, v} n K) (hn : 0 < n) :
    IsAbFaithful Gal(AlgebraicClosure K/K) := by
  have : T2Space Gal(SeparableClosure K/K) :=
    krullTopology_t2 (K := K) (L := SeparableClosure K)
  have hSep : IsSigmaAbFaithful {p} Gal(SeparableClosure K/K) := by
    apply isSigmaAbFaithful_iff_prime_order_test.mpr
    intro H
    have : CompactSpace (H : Subgroup Gal(SeparableClosure K/K)) :=
      H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
    intro N hprime
    have hfaith := higherLocal_openLayer_residual_faithful n p hK hn H N hprime
    exact (injective_iff_ne_one_of_prime_card _ hprime).mp hfaith
  exact (IsSigmaAbFaithful.of_continuousMulEquiv
    (ValuationTheory.Completion.separableClosureAutContinuousEquiv K) hSep).isAbFaithful

end Yamaguchi26AbfaithfulGalois
