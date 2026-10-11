/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaAllPrimes
import Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaMaximalQuotient
import ProCGroups.ProC.Quotients.ClosedNormal
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# Remark 1.3: properties of `Σ`-ab-faithfulness

TeX label: `prop:sigma-ab-faithful-properties`. The first conjunct also
records the all-primes identification stated with the definition.
-/

noncomputable section

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups ProCGroups.ProC
open ProCGroups.FiniteStepSolvableQuotients

universe u

/-- Allowing all primes recovers ordinary ab-faithfulness. Enlarging `Σ`
preserves `Σ`-ab-faithfulness, and the maximal pro-`Σ` quotient inherits it.
For a singleton set of primes, both the original group and its maximal
pro-`ℓ` quotient are ordinarily ab-faithful. -/
theorem sigma_properties_1_3
    {sigma : Set ℕ} (G : ProfiniteGrp.{u}) :
    (IsSigmaAbFaithful Set.univ G ↔ IsAbFaithful G) ∧
      (IsSigmaAbFaithful sigma G →
        let Q := G ⧸ proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G
        letI : TotallyDisconnectedSpace Q :=
          totallyDisconnectedSpace_quotient_closedNormal
            (proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G)
            (proCResidualCore_isClosed (FiniteGroupClass.sigmaGroup sigma) G)
        (∀ tau : Set ℕ, sigma ⊆ tau → IsSigmaAbFaithful tau G) ∧
          IsSigmaAbFaithful sigma Q ∧
          (∀ ell : ℕ, sigma = {ell} →
            IsAbFaithful G ∧ IsAbFaithful Q)) := by
  refine ⟨isSigmaAbFaithful_univ_iff (G := G), ?_⟩
  intro hG
  let Q := G ⧸ proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G
  let : TotallyDisconnectedSpace Q :=
    totallyDisconnectedSpace_quotient_closedNormal
      (proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G)
      (proCResidualCore_isClosed (FiniteGroupClass.sigmaGroup sigma) G)
  change (∀ tau : Set ℕ, sigma ⊆ tau → IsSigmaAbFaithful tau G) ∧
    IsSigmaAbFaithful sigma Q ∧
    (∀ ell : ℕ, sigma = {ell} → IsAbFaithful G ∧ IsAbFaithful Q)
  have hQ : IsAbFaithful Q := hG.isAbFaithful_residualQuotient
  refine ⟨?_, ?_, ?_⟩
  · intro tau hsub
    exact IsSigmaAbFaithful.mono hsub hG
  · exact (isSigmaAbFaithful_iff_isAbFaithful_of_proSigma
      (G := Q) (sigma := sigma)
      (proCResidualCoreQuotient_hasOpenNormalBasisInClass
        (G := G) (FiniteGroupClass.sigmaGroup_formation sigma))).2 hQ
  · intro ell _
    exact ⟨hG.isAbFaithful, hQ⟩

end Yamaguchi26AbfaithfulGalois
