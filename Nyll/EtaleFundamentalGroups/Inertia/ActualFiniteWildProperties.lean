/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteWildSubgroup
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteWildOrder
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameIndex
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Primary, characteristic-zero and index laws for actual finite wild inertia

The normalization group and field constructors are already closed. These
proofs use only the actual subgroup's cardinality, actual tame/wild orders,
and the original residue field.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [rA : CommRing A] [dA : IsDomain A] [vA : IsDiscreteValuationRing A]
  [fK : Field K] [fL : Field L] [aAK : Algebra A K] [frAK : IsFractionRing A K]
  [aKL : Algebra K L] [aAL : Algebra A L] [tAKL : IsScalarTower A K L] [gKL : IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [qMax : Q.IsMaximal]

/-- The SAME actual finite wild subgroup has power-of-p cardinality. -/
theorem actualFiniteWildSubgroup_card_exists_pow_of_baseResidue_charP
    (E : FiniteGaloisIntermediateField K L)
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    ∃ n : ℕ, Nat.card (actualFiniteWildSubgroup A K L Q E) = p ^ n := by
  obtain ⟨n, hn⟩ := actualFiniteStageWildOrder_exists_baseResidue_expChar_pow A K L Q E
  refine ⟨n, (actualFiniteWildSubgroup_card A K L Q E).trans (hn.trans ?_)⟩
  exact congrArg (fun q : ℕ => q ^ n) (ringExpChar.eq (IsLocalRing.ResidueField A) p)

/-- Its cardinality supplies the p-group property. -/
theorem actualFiniteWildSubgroup_isPGroup_of_baseResidue_charP
    (E : FiniteGaloisIntermediateField K L)
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    IsPGroup p (actualFiniteWildSubgroup A K L Q E) := by
  obtain ⟨n, hn⟩ := actualFiniteWildSubgroup_card_exists_pow_of_baseResidue_charP A K L Q E p
  exact IsPGroup.of_card hn

/-- In characteristic zero of the original base residue field, the same
actual intrinsic finite wild subgroup is trivial. -/
theorem actualFiniteWildSubgroup_eq_bot_of_baseResidue_charZero
    (E : FiniteGaloisIntermediateField K L) [CharZero (IsLocalRing.ResidueField A)] :
    actualFiniteWildSubgroup A K L Q E = ⊥ := by
  obtain ⟨n, hn⟩ := actualFiniteStageWildOrder_exists_baseResidue_expChar_pow A K L Q E
  apply Subgroup.eq_bot_of_card_eq
  exact (actualFiniteWildSubgroup_card A K L Q E).trans
    (hn.trans (by rw [ringExpChar.eq_one, one_pow]))

/-- The actual intrinsic wild index is invertible in the original DVR. -/
theorem actualFiniteWildSubgroup_index_isUnit (E : FiniteGaloisIntermediateField K L) :
    IsUnit ((actualFiniteWildSubgroup A K L Q E).index : A) := by
  rw [actualFiniteWildSubgroup_index]
  exact actualFiniteStageTameOrder_isUnit A K L Q E

/-- The same subgroup has index prime to the original residue characteristic. -/
theorem actualFiniteWildSubgroup_index_not_dvd_of_baseResidue_charP
    (E : FiniteGaloisIntermediateField K L) :
    ∀ (p : ℕ) [CharP (IsLocalRing.ResidueField A) p],
      ¬ p ∣ (actualFiniteWildSubgroup A K L Q E).index := by
  let n : ℕ := (actualFiniteWildSubgroup A K L Q E).index
  have hu : IsUnit (n : A) := actualFiniteWildSubgroup_index_isUnit A K L Q E
  change ∀ (p : ℕ) [CharP (IsLocalRing.ResidueField A) p], ¬ p ∣ n
  clear_value n
  clear actualFiniteWildSubgroup_index_not_dvd_of_baseResidue_charP
  clear qMax Q E gKL tAKL aAL aKL frAK aAK fL L fK K
  intro p hchar
  have hresidue : IsUnit (n : IsLocalRing.ResidueField A) := by
    simpa only [map_natCast] using hu.map (IsLocalRing.residue A)
  intro hdiv
  exact hresidue.ne_zero
    ((CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) p n).mpr hdiv)

end EtaleFundamentalGroups.Inertia

end
