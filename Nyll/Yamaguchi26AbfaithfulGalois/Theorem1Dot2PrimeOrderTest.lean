/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaPrimeOrderTest
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.PrimePowerCharacterDetection
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualAbelianizationPrimePowers
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# Lemma 1.2: the prime-order test

Source: [Yamaguchi, arXiv:2610.05634v1](https://arxiv.org/abs/2610.05634v1), Lemma 1.2.
Condition (iii) is expressed directly
in the abelianization: two classes agree modulo `ℓ ^ s` precisely when
they differ by an `ℓ ^ s`-th power. The prime order of `H/N` is not
restricted to `Σ`.
-/

noncomputable section

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups ProCGroups.ProC ProCGroups.Abelian
open ProCGroups.FiniteStepSolvableQuotients

universe u

/-- The paper's four equivalent conditions: `Σ`-ab-faithfulness,
nontriviality on prime-order layers of the abelianized pro-`Σ` quotient,
nontriviality of some `ℓ ^ s`-modular abelianization action, and
nontriviality on continuous H¹, identified with continuous characters. -/
theorem prime_order_test_1_2
    {sigma : Set ℕ} (G : ProfiniteGrp.{u}) :
    let residualTest : Prop :=
      ∀ H : OpenSubgroup G,
        letI : CompactSpace (H : Subgroup G) :=
          H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
        ∀ N : OpenNormalSubgroup (H : Subgroup G),
          Nat.Prime (Nat.card ((H : Subgroup G) ⧸
            (N : Subgroup (H : Subgroup G)))) →
            residualAbelianizationQuotientConjugation
              (FiniteGroupClass.sigmaGroup_fullFormation sigma)
              (N : Subgroup (H : Subgroup G)) N.isClosed ≠ 1
    let powerTest : Prop :=
      ∀ H : OpenSubgroup G,
        ∀ N : OpenNormalSubgroup (H : Subgroup G),
          Nat.Prime (Nat.card ((H : Subgroup G) ⧸
            (N : Subgroup (H : Subgroup G)))) →
            ∃ ell : ℕ, ell ∈ sigma ∧ Nat.Prime ell ∧
              ∃ s : ℕ, 0 < s ∧
                ∃ g : ((H : Subgroup G) ⧸ (N : Subgroup (H : Subgroup G))),
                  g ≠ 1 ∧
                    ∃ a : TopologicalAbelianization
                        (N : Subgroup (H : Subgroup G)),
                      ¬ ∃ b : TopologicalAbelianization
                          (N : Subgroup (H : Subgroup G)),
                        quotientConjugationTopologicalAbelianizationMap
                            (N := (N : Subgroup (H : Subgroup G))) g a =
                          a * b ^ (ell ^ s)
    let cohomologyTest : Prop :=
      ∀ H : OpenSubgroup G,
        ∀ N : OpenNormalSubgroup (H : Subgroup G),
          Nat.Prime (Nat.card ((H : Subgroup G) ⧸
            (N : Subgroup (H : Subgroup G)))) →
            ∃ ell : ℕ, ell ∈ sigma ∧ Nat.Prime ell ∧
              ∃ s : ℕ, 0 < s ∧
                ∃ (g : (H : Subgroup G))
                  (χ : (N : Subgroup (H : Subgroup G)) →ₜ*
                    Multiplicative (ZMod (ell ^ s)))
                  (n : (N : Subgroup (H : Subgroup G))),
                  χ (MulAut.conjNormal g n) ≠ χ n
    (IsSigmaAbFaithful sigma G ↔ residualTest) ∧
      (residualTest ↔ powerTest) ∧ (powerTest ↔ cohomologyTest) := by
  refine ⟨isSigmaAbFaithful_iff_prime_order_test (sigma := sigma) (G := G), ?_, ?_⟩
  · constructor
    · intro hres H N hdegree
      have : CompactSpace (H : Subgroup G) :=
        H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
      by_contra hnone
      push Not at hnone
      apply hres H N hdegree
      apply (residualAbelianizationQuotientConjugation_eq_one_iff_primePower
        (sigma := sigma) (N : Subgroup (H : Subgroup G)) N.isClosed).mpr
      intro g a ell hellsigma hell s hs
      by_cases hg : g = 1
      · refine ⟨1, ?_⟩
        simp only [hg, map_one, MulAut.one_apply, one_pow, mul_one]
      · exact hnone ell hellsigma hell s hs g hg a
    · intro hpower H N hdegree
      have : CompactSpace (H : Subgroup G) :=
        H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
      obtain ⟨ell, hellsigma, hell, s, hs, g, _, a, ha⟩ := hpower H N hdegree
      intro htrivial
      exact ha ((residualAbelianizationQuotientConjugation_eq_one_iff_primePower
        (sigma := sigma) (N : Subgroup (H : Subgroup G)) N.isClosed).mp
          htrivial g a ell hellsigma hell s hs)
  · constructor
    · intro hpower H N hdegree
      have : CompactSpace (H : Subgroup G) :=
        H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
      have : CompactSpace (N : Subgroup (H : Subgroup G)) :=
        N.isClosed.isClosedEmbedding_subtypeVal.compactSpace
      have : TotallyDisconnectedSpace (TopologicalAbelianization
          (N : Subgroup (H : Subgroup G))) :=
        ProCGroups.totallyDisconnectedSpace_quotient_closedNormal _
          (Subgroup.isClosed_closedCommutator _)
      obtain ⟨ell, hellsigma, hell, s, hs, g, hg, a, ha⟩ := hpower H N hdegree
      have : Fact ell.Prime := ⟨hell⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
        (N : Subgroup (H : Subgroup G)) g
      obtain ⟨n, rfl⟩ := TopologicalAbelianization.surjective_mk _ a
      let b := TopologicalAbelianization.mk _ (MulAut.conjNormal g n)
      let a := TopologicalAbelianization.mk _ n
      have hdiff : ¬ ∃ z : TopologicalAbelianization (N : Subgroup (H : Subgroup G)),
          z ^ (ell ^ s) = b * a⁻¹ := by
        rintro ⟨z, hz⟩
        apply ha
        refine ⟨z, ?_⟩
        change b = a * z ^ (ell ^ s)
        rw [hz, mul_comm b, ← mul_assoc, mul_inv_cancel, one_mul]
      obtain ⟨k, hk, χ, hχ⟩ := exists_primePower_character_of_not_pow ell s
        (b * a⁻¹) hdiff
      refine ⟨ell, hellsigma, hell, k, hk, g,
        χ.comp (TopologicalAbelianization.mkₜ _), n, ?_⟩
      intro heq
      apply hχ
      rw [map_mul, map_inv, show χ b = χ a from heq, mul_inv_cancel]
    · intro hcoh H N hdegree
      obtain ⟨ell, hellsigma, hell, s, hs, g, χ, n, hχ⟩ := hcoh H N hdegree
      let a := TopologicalAbelianization.mk _ n
      let gbar := QuotientGroup.mk' (N : Subgroup (H : Subgroup G)) g
      have hg : gbar ≠ 1 := by
        intro h
        apply hχ
        have hfixed := congrArg (fun e => e a)
          (show quotientConjugationTopologicalAbelianizationMap
            (N := (N : Subgroup (H : Subgroup G))) gbar = 1 from by rw [h, map_one])
        exact congrArg (TopologicalAbelianization.lift χ) hfixed
      refine ⟨ell, hellsigma, hell, s, hs, gbar, hg, a, ?_⟩
      rintro ⟨b, hb⟩
      apply hχ
      have heq := congrArg (TopologicalAbelianization.lift χ) hb
      have hpow : (TopologicalAbelianization.lift χ b) ^ (ell ^ s) = 1 := by
        apply Multiplicative.toAdd.injective
        change (ell ^ s) • (TopologicalAbelianization.lift χ b).toAdd = 0
        simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      simpa only [map_mul, map_pow, hpow, mul_one, gbar, a,
        quotientConjugationTopologicalAbelianizationMap_mk_apply_mk,
        TopologicalAbelianization.lift_apply_mk] using heq

end Yamaguchi26AbfaithfulGalois
