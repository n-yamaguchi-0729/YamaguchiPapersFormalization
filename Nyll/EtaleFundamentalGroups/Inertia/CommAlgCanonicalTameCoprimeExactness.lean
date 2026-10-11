/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.CommAlgCanonicalTameMorphism
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealWildSubgroup
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTamePrimitiveRoots
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameProperties
import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameExactness
import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealCanonicalTameCharacter
import Nyll.SchemeTheory.RingTheory.Localization.DedekindPrime
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Exactness of the SAME canonical character from normalization coprimality

The existing primitive root determines the full root-group cardinality.
Mathlib's coprime-power bijection then proves that the actual e/n power
normalization preserves surjectivity and the independently defined wild kernel.
-/

open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- Coprimality of the actual tame order and actual e/n normalization exponent
makes the SAME normalized character onto with its SAME principal-unit kernel. -/
theorem commAlgCanonicalTameMorphism_exact_of_coprime
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B.carrier] [Finite (B.carrier ≃ₐ[A] B.carrier)]
    (q : Ideal B.carrier) [q.IsPrime] (hq : q ≠ ⊥)
    (hcop : Nat.Coprime (commAlgIdealTameOrder A B q hq)
      (q.ramificationIdx A / commAlgIdealTameOrder A B q hq)) :
    Function.Surjective (commAlgCanonicalTameMorphism A B q hq).hom'.toFun ∧
      (commAlgCanonicalTameMorphism A B q hq).hom'.ker =
        commAlgIdealWildSubgroup A B q hq := by
  have hn : NeZero (commAlgIdealTameOrder A B q hq) :=
    ⟨(commAlgIdealTameOrder_pos A B q hq).ne'⟩
  obtain ⟨ζ, hζ⟩ := commAlgIdealTameOrder_exists_primitiveRoot A B q hq
  have hcard : Nat.card (rootsOfUnity (commAlgIdealTameOrder A B q hq) q.ResidueField) =
      commAlgIdealTameOrder A B q hq := hζ.card_rootsOfUnity
  let power : rootsOfUnity (commAlgIdealTameOrder A B q hq) q.ResidueField →*
      rootsOfUnity (commAlgIdealTameOrder A B q hq) q.ResidueField :=
    powMonoidHom (q.ramificationIdx A / commAlgIdealTameOrder A B q hq)
  have hpower : Function.Bijective power.toFun := by
    apply Nat.Coprime.pow_left_bijective
    rw [hcard]
    exact hcop
  have dR : IsDiscreteValuationRing (Localization.AtPrime q) :=
    SchemeTheory.localizationAtPrime_isDiscreteValuationRing B.carrier q hq
  change Function.Surjective
      (power.comp (finiteIdealTameCharacterGroupMap B.carrier
        (B.carrier ≃ₐ[A] B.carrier) q hq)).toFun ∧
    (power.comp (finiteIdealTameCharacterGroupMap B.carrier
      (B.carrier ≃ₐ[A] B.carrier) q hq)).ker =
        finiteIdealWildSubgroup B.carrier (B.carrier ≃ₐ[A] B.carrier) q hq
  constructor
  · exact hpower.2.comp
      (finiteIdealTameCharacterGroupMap_surjective B.carrier
        (B.carrier ≃ₐ[A] B.carrier) q hq)
  · exact (MonoidHom.ker_comp_of_injective _ _ hpower.1).trans
      (finiteIdealTameCharacterGroupMap_ker B.carrier
        (B.carrier ≃ₐ[A] B.carrier) q hq)

end EtaleFundamentalGroups.Inertia
