/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgIdealTameOrder
import EtaleFundamentalGroups.Inertia.CommAlgIdealTameProperties
import EtaleFundamentalGroups.Inertia.FiniteIdealTameCharacter
import EtaleFundamentalGroups.Inertia.FiniteIdealTameExactness
import EtaleFundamentalGroups.Inertia.FiniteIdealTameQuotientCardinality
import EtaleFundamentalGroups.Inertia.FiniteIdealWildPrimary
import EtaleFundamentalGroups.Inertia.NormalizationResidueCharacteristic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.PGroup
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Intrinsic wild subgroup laws on one coefficient algebra

The subgroup is literally the existing principal-unit subgroup in native
coefficient-automorphism inertia. Its primary order, character kernel and
tame quotient cardinality supply the three Sylow image inputs. No field
presentation or comparison premise is introduced.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- The existing intrinsic principal-unit wild subgroup is a p-group for
the characteristic of the original base residue field. -/
theorem commAlgIdealWildSubgroup_isPGroup_of_baseResidue_charP
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    (B : CommAlgCat.{v} A) [IsDedekindDomain B.carrier]
    [Module.Finite A B.carrier] [Module.IsTorsionFree A B.carrier]
    (Q : Ideal B.carrier) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal A)] (hQ : Q ≠ ⊥)
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    IsPGroup p (finiteIdealWildSubgroup B.carrier
      (B.carrier ≃ₐ[A] B.carrier) Q hQ) := by
  obtain ⟨n, hn⟩ := finiteIdealWildOrder_exists_expChar_pow A B.carrier Q hQ
  have hcard : Nat.card (finiteIdealWildSubgroup B.carrier
      (B.carrier ≃ₐ[A] B.carrier) Q hQ) = (ringExpChar Q.ResidueField) ^ n :=
    (finiteIdealWildSubgroup_card B.carrier
      (B.carrier ≃ₐ[A] B.carrier) Q hQ).trans hn
  have hchar : ringExpChar Q.ResidueField = p :=
    (idealResidue_ringExpChar_eq_baseResidue A B.carrier Q).trans
      (ringExpChar.eq (IsLocalRing.ResidueField A) p)
  exact IsPGroup.of_card (hcard.trans (congrArg (fun q : ℕ => q ^ n) hchar))

/-- The same intrinsic wild subgroup is normal because it is the proved
kernel of the actual finite ideal tame character. -/
theorem commAlgIdealWildSubgroup_normal
    (A : Type u) [CommRing A]
    (B : CommAlgCat.{v} A) [IsDedekindDomain B.carrier]
    [Finite (B.carrier ≃ₐ[A] B.carrier)]
    (Q : Ideal B.carrier) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    (finiteIdealWildSubgroup B.carrier
      (B.carrier ≃ₐ[A] B.carrier) Q hQ).Normal := by
  rw [← finiteIdealTameCharacterGroupMap_ker B.carrier
    (B.carrier ≃ₐ[A] B.carrier) Q hQ]
  exact MonoidHom.normal_ker
    (finiteIdealTameCharacterGroupMap B.carrier
      (B.carrier ≃ₐ[A] B.carrier) Q hQ)

/-- Its literal index is the existing tame quotient cardinality and is
therefore invertible in the original local coefficient ring. -/
theorem commAlgIdealWildSubgroup_index_isUnit
    (A : Type u) [CommRing A] [IsLocalRing A]
    (B : CommAlgCat.{v} A) [IsDedekindDomain B.carrier]
    [Finite (B.carrier ≃ₐ[A] B.carrier)]
    (Q : Ideal B.carrier) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal A)] (hQ : Q ≠ ⊥) :
    IsUnit ((finiteIdealWildSubgroup B.carrier
      (B.carrier ≃ₐ[A] B.carrier) Q hQ).index : A) := by
  have hindex : (finiteIdealWildSubgroup B.carrier
      (B.carrier ≃ₐ[A] B.carrier) Q hQ).index =
        commAlgIdealTameOrder A B Q hQ :=
    (finiteIdealTameOrder_eq_card_quotient_wild B.carrier
      (B.carrier ≃ₐ[A] B.carrier) Q hQ).symm
  rw [hindex]
  exact commAlgIdealTameOrder_isUnit A B Q hQ

/-- The same intrinsic wild subgroup has prime-to-characteristic index.
Only the already proved base-ring unit enters the residue calculation. -/
theorem commAlgIdealWildSubgroup_index_not_dvd_of_baseResidue_charP
    (A : Type u) [CommRing A] [IsLocalRing A]
    (B : CommAlgCat.{v} A) [IsDedekindDomain B.carrier]
    [Finite (B.carrier ≃ₐ[A] B.carrier)]
    (Q : Ideal B.carrier) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal A)] (hQ : Q ≠ ⊥)
    (p : ℕ) [CharP (IsLocalRing.ResidueField A) p] :
    ¬ p ∣ (finiteIdealWildSubgroup B.carrier
      (B.carrier ≃ₐ[A] B.carrier) Q hQ).index := by
  have hu : IsUnit ((finiteIdealWildSubgroup B.carrier
      (B.carrier ≃ₐ[A] B.carrier) Q hQ).index : A) :=
    commAlgIdealWildSubgroup_index_isUnit A B Q hQ
  have hresidue : IsUnit ((finiteIdealWildSubgroup B.carrier
      (B.carrier ≃ₐ[A] B.carrier) Q hQ).index : IsLocalRing.ResidueField A) := by
    simpa only [map_natCast] using hu.map (IsLocalRing.residue A)
  intro hdiv
  exact hresidue.ne_zero
    ((CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) p
      (finiteIdealWildSubgroup B.carrier
        (B.carrier ≃ₐ[A] B.carrier) Q hQ).index).mpr hdiv)

end EtaleFundamentalGroups.Inertia

end
