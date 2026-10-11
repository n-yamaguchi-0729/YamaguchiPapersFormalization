/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.SeparablyClosedFractionResidue
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# The literal maximal quotient in the absolute residue-closure argument

The established separably closed fraction-field theorem applies to the
prime residue field. At a maximal ideal its canonical quotient map is
bijective, so algebraic closedness transfers to the actual quotient. A
separate integral-ring owner proves algebraicity over the contracted
quotient, without carrying the fraction field or its scalar structures.

Reference: Stacks Project, Tag 0BUB.
https://stacks.math.columbia.edu/tag/0BUB
-/

namespace EtaleFundamentalGroups.Inertia

universe u v

attribute [local instance] Ideal.Quotient.field

/-- The canonical map identifies a maximal quotient with the prime residue
field, so splitting transfers to the literal quotient. -/
private theorem maximalQuotient_isAlgClosed_of_primeResidueField
    (B : Type u) [CommRing B] (Q : Ideal B) [Q.IsMaximal]
    [IsAlgClosed Q.ResidueField] : IsAlgClosed (B ⧸ Q) := by
  constructor
  intro f
  apply Polynomial.Splits.of_splits_map (algebraMap (B ⧸ Q) Q.ResidueField)
    (IsAlgClosed.splits (f.map (algebraMap (B ⧸ Q) Q.ResidueField)))
  intro x hx
  exact Q.bijective_algebraMap_quotient_residueField.surjective x

/-- The literal maximal quotient of a normal domain with separably closed
fraction field is algebraically closed whenever the maximal ideal is
nonzero. No perfectness or residue characteristic assumption is made. -/
theorem maximalQuotient_isAlgClosed_of_isSepClosed_fractionRing
    (B : Type u) (Ω : Type v) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Field Ω] [Algebra B Ω] [IsFractionRing B Ω] [IsSepClosed Ω]
    (Q : Ideal B) [Q.IsMaximal] (hQ : Q ≠ ⊥) : IsAlgClosed (B ⧸ Q) := by
  have : IsAlgClosed Q.ResidueField :=
    StrictHenselian.isAlgClosed_primeResidueField_of_isSepClosed_fractionRing B Ω Q hQ
  exact maximalQuotient_isAlgClosed_of_primeResidueField B Q

/-- Integrality descends to the actual quotient by a maximal ideal and
its contraction. Thus an algebraically closed upper quotient is an
algebraic closure of the lower quotient. -/
theorem maximalQuotient_isAlgClosure_of_isIntegral
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (Q : Ideal B) [Q.IsMaximal]
    [IsAlgClosed (B ⧸ Q)] : IsAlgClosure (A ⧸ Q.under A) (B ⧸ Q) := by
  have : Algebra.IsIntegral A (B ⧸ Q) :=
    Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ A Q) Ideal.Quotient.mk_surjective
  have : Algebra.IsIntegral (A ⧸ Q.under A) (B ⧸ Q) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := A) x).tower_top⟩
  exact ⟨inferInstance, inferInstance⟩

end EtaleFundamentalGroups.Inertia
