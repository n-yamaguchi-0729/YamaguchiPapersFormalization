/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.HenselianAbsoluteGalois
import Nyll.ProCGroups.FiniteGroups.StandardClasses
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualEquivalence
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.Faithful
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Absolute Galois groups and their pro-p quotients across completion

The maximal pro-p quotient is the actual quotient by the pro-p residual
core. The absolute Galois comparison carries this core onto the corresponding
core of the completion, giving a continuous group isomorphism and preserving
ab-faithfulness in every characteristic.
-/

noncomputable section

namespace Yamaguchi26AbfaithfulGalois

open ValuationTheory.DiscreteValuationField
open ProCGroups ProCGroups.ProC ProCGroups.FiniteStepSolvableQuotients

universe u

/-- Completion identifies the actual maximal pro-p quotients of the absolute
Galois groups. The prime need not equal the residue characteristic. -/
def completionMaximalProPGaloisEquiv
    {K : Type u} [Field K] (base : HenselianDVF K) (p : ℕ) [Fact p.Prime] :
    (Field.absoluteGaloisGroup K ⧸
      proCResidualCore (FiniteGroupClass.pGroup p) (Field.absoluteGaloisGroup K)) ≃ₜ*
    (Field.absoluteGaloisGroup base.valuation.Completion ⧸
      proCResidualCore (FiniteGroupClass.pGroup p)
        (Field.absoluteGaloisGroup base.valuation.Completion)) := by
  let e : Field.absoluteGaloisGroup K ≃ₜ*
      Field.absoluteGaloisGroup base.valuation.Completion :=
    base.completionAbsoluteGaloisEquiv
      (IsSepClosed.lift : SeparableClosure K →ₐ[K] SeparableClosure base.valuation.Completion)
  let r : Field.absoluteGaloisGroup K ≃ₜ* Gal(SeparableClosure K/K) :=
    ValuationTheory.Completion.separableClosureAutContinuousEquiv K
  have : IsGalois K (SeparableClosure K) :=
    IsSepClosure.isGalois (k := K) (K := SeparableClosure K)
  have : CompactSpace (Field.absoluteGaloisGroup K) := r.symm.toHomeomorph.compactSpace
  have : T2Space (Field.absoluteGaloisGroup K) := r.toHomeomorph.isEmbedding.t2Space
  have : CompactSpace (Field.absoluteGaloisGroup base.valuation.Completion) :=
    e.toHomeomorph.compactSpace
  have : T2Space (Field.absoluteGaloisGroup base.valuation.Completion) :=
    e.symm.toHomeomorph.isEmbedding.t2Space
  exact residualQuotientContinuousMulEquiv (C := FiniteGroupClass.pGroup p)
    (FiniteGroupClass.pGroup_hereditary p) e

/-- Ab-faithfulness of the maximal pro-p absolute Galois quotient of a
Henselian DVF is equivalent to that of its actual completion. -/
theorem isAbFaithful_maximalProPGaloisGroup_iff_completion
    {K : Type u} [Field K] (base : HenselianDVF K) (p : ℕ) [Fact p.Prime] :
    IsAbFaithful (Field.absoluteGaloisGroup K ⧸
      proCResidualCore (FiniteGroupClass.pGroup p) (Field.absoluteGaloisGroup K)) ↔
    IsAbFaithful (Field.absoluteGaloisGroup base.valuation.Completion ⧸
      proCResidualCore (FiniteGroupClass.pGroup p)
        (Field.absoluteGaloisGroup base.valuation.Completion)) :=
  isAbFaithful_iff_continuousMulEquiv (completionMaximalProPGaloisEquiv base p)

/-- Ab-faithfulness of the absolute Galois group of a Henselian DVF is
equivalent to that of its completion, in every characteristic. -/
theorem isAbFaithful_absoluteGaloisGroup_iff_completion
    {K : Type u} [Field K] (base : HenselianDVF K) :
    IsAbFaithful (Field.absoluteGaloisGroup K) ↔
      IsAbFaithful (Field.absoluteGaloisGroup base.valuation.Completion) :=
  isAbFaithful_iff_continuousMulEquiv
    (base.completionAbsoluteGaloisEquiv
      (IsSepClosed.lift : SeparableClosure K →ₐ[K] SeparableClosure base.valuation.Completion))

end Yamaguchi26AbfaithfulGalois
