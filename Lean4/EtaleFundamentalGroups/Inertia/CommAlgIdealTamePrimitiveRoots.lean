/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgIdealTameOrder
import SchemeTheory.RingTheory.Localization.DedekindPrime
import ValuedFieldTheory.Ramification.HilbertRamification.RingFiniteTameCharacter
import ValuedFieldTheory.Ramification.HilbertRamification.RootsOfUnityFieldEmbedding
import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Primitive roots of native finite tame orders

The actual local inertia-character image supplies a primitive root of the
intrinsic tame order. Consequently its full root group is preserved by
every residue-field embedding.
-/

namespace EtaleFundamentalGroups.Inertia

open scoped Pointwise

open RamificationTheory.HilbertRamification

universe u v w

variable (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
  [IsDedekindDomain B] [Finite (B ≃ₐ[A] B)]
  (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)

/-- The SAME intrinsic finite tame order occurs as a primitive root in
the literal residue field of its normalization prime. -/
theorem commAlgIdealTameOrder_exists_primitiveRoot :
    ∃ ζ : Q.ResidueField, IsPrimitiveRoot ζ (commAlgIdealTameOrder A B Q hQ) := by
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
  exact DiscreteValuationRing.exists_primitiveRoot_tameOrder
    (Localization.AtPrime Q) (MulAction.stabilizer (B ≃ₐ[A] B) Q)

/-- The full tame-degree root group already contains every root after a
field embedding, by the primitive-root cardinality bound. -/
theorem commAlgIdealTameRoots_bijective
    (k : Type w) [Field k] (f : Q.ResidueField →+* k) :
    Function.Bijective (restrictRootsOfUnity f (commAlgIdealTameOrder A B Q hQ)) := by
  have : NeZero (commAlgIdealTameOrder A B Q hQ) :=
    ⟨(finiteIdealTameOrder_pos B (B ≃ₐ[A] B) Q hQ).ne'⟩
  exact restrictRootsOfUnity_bijective_of_primitiveRoot f
    (commAlgIdealTameOrder A B Q hQ)
    (commAlgIdealTameOrder_exists_primitiveRoot A B Q hQ)

end EtaleFundamentalGroups.Inertia
