/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteFieldCanonicalTameExactness
import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteFieldWildCardinality
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationResidueCharacteristic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.PGroup

/-!
# Original finite wild inertia over the base residue characteristic

The independent original-field wild subgroup has prime-power cardinality for
the characteristic of the base DVR residue field. The same subgroup is a
p-group in positive residue characteristic and is trivial when that base
residue field has characteristic zero.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- The original finite-field wild subgroup has power cardinality for the
exponential characteristic of the original base residue field. -/
theorem originalFiniteFieldWildSubgroup_card_exists_baseResidue_expChar_pow
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal] :
    ∃ r : ℕ, Nat.card (originalFiniteFieldWildSubgroup A K F Q) =
      (ringExpChar (IsLocalRing.ResidueField A)) ^ r := by
  obtain ⟨r, hr⟩ := originalFiniteFieldWildSubgroup_card_exists_expChar_pow A K F Q
  exact ⟨r, hr.trans (congrArg (fun p : ℕ => p ^ r)
    (normalizationResidue_ringExpChar_eq_baseResidue A F Q))⟩

/-- For the positive prime characteristic of the base residue field, the
SAME original finite-field wild subgroup has a power-of-p cardinality. -/
theorem originalFiniteFieldWildSubgroup_card_exists_pow_of_baseResidue_charP
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    ∃ r : ℕ, Nat.card (originalFiniteFieldWildSubgroup A K F Q) = p ^ r := by
  obtain ⟨r, hr⟩ := originalFiniteFieldWildSubgroup_card_exists_baseResidue_expChar_pow A K F Q
  exact ⟨r, hr.trans (by rw [ringExpChar.eq (IsLocalRing.ResidueField A) p])⟩

/-- The independent original-field wild group is a p-group for the prime
characteristic of the original base residue field. -/
theorem originalFiniteFieldWildSubgroup_isPGroup_of_baseResidue_charP
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    IsPGroup p (originalFiniteFieldWildSubgroup A K F Q) := by
  obtain ⟨r, hr⟩ :=
    originalFiniteFieldWildSubgroup_card_exists_pow_of_baseResidue_charP A K F Q p
  exact IsPGroup.of_card hr

/-- In characteristic zero of the base residue field, the SAME original
finite-field wild subgroup is trivial. -/
theorem originalFiniteFieldWildSubgroup_eq_bot_of_baseResidue_charZero
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal]
    [CharZero (IsLocalRing.ResidueField A)] :
    originalFiniteFieldWildSubgroup A K F Q = ⊥ := by
  obtain ⟨r, hr⟩ := originalFiniteFieldWildSubgroup_card_exists_baseResidue_expChar_pow A K F Q
  apply Subgroup.eq_bot_of_card_eq
  exact hr.trans (by rw [ringExpChar.eq_one, one_pow])

end EtaleFundamentalGroups.Inertia

end
