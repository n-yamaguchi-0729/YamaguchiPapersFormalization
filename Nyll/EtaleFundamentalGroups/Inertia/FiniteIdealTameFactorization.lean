/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameOrder
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteInertiaCardinality
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Tame and wild orders with inseparable residue degree

The actual finite tame and principal-unit wild orders multiply to the
ramification index times the inseparable degree of the native residue
extension. The existential factorization interface follows from this explicit
identity.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v w

attribute [local instance] Ideal.Quotient.field

/-- The actual original finite tame and wild orders satisfy the ramification
identity with the inseparable degree of the actual residue extension. Both
residue fields and their coefficient action are the native ideal quotients. -/
theorem finiteIdealTameOrder_mul_wildOrder_eq_ramificationIdx_mul_finInsepDegree
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver (IsLocalRing.maximalIdeal A)] (hQ : Q ≠ ⊥)
    (G : Type w) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B] :
    finiteIdealTameOrder B G Q hQ * finiteIdealWildOrder B G Q hQ =
      Q.ramificationIdx A *
        Field.finInsepDegree (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ Q) := by
  calc
    finiteIdealTameOrder B G Q hQ * finiteIdealWildOrder B G Q hQ =
        Nat.card (Q.inertia G) := (finiteIdealInertia_card_eq_tame_mul_wild B G Q hQ).symm
    _ = Q.ramificationIdx A *
        Field.finInsepDegree (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ Q) :=
      HilbertRamification.Dedekind.inertia_card_eq_ramificationIdx_mul_finInsepDegree
        (IsLocalRing.maximalIdeal A) (IsDiscreteValuationRing.not_a_field A) Q G

/-- The original existential interface follows from the explicit inseparable
residue-degree identity. -/
theorem finiteIdealTameOrder_mul_wildOrder_eq_ramificationIdx_mul
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver (IsLocalRing.maximalIdeal A)] (hQ : Q ≠ ⊥)
    (G : Type w) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B] :
    ∃ f : ℕ, finiteIdealTameOrder B G Q hQ * finiteIdealWildOrder B G Q hQ =
      Q.ramificationIdx A * f :=
  ⟨Field.finInsepDegree (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ Q),
    finiteIdealTameOrder_mul_wildOrder_eq_ramificationIdx_mul_finInsepDegree A B Q hQ G⟩

end EtaleFundamentalGroups.Inertia
