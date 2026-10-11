/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteWildSubgroup
import EtaleFundamentalGroups.Inertia.ActualFiniteWildProperties
import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaTowerRestriction
import EtaleFundamentalGroups.Inertia.ActualFiniteTameGroups
import EtaleFundamentalGroups.Inertia.FiniteWildImage
import SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.PGroup
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Actual finite wild subgroup images

Actual intrinsic finite inertia restriction is onto. The SAME actual wild
subgroups have proved primary cardinalities, prime-to-characteristic indices
and target normality. The original field environment is closed before the
finite-group Sylow image theorem is applied.
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
  (E F : FiniteGaloisIntermediateField K L) (hEF : E ≤ F)

/-- Actual intrinsic inertia restriction has exactly the actual wild image
in positive residue characteristic. -/
theorem actualFiniteWildSubgroup_map_of_baseResidue_charP
    (p : ℕ) [hp : Fact p.Prime] [charA : CharP (IsLocalRing.ResidueField A) p] :
    (actualFiniteWildSubgroup A K L Q F).map
        (actualFiniteInertiaTowerRestriction A K L Q E F hEF).hom' =
      actualFiniteWildSubgroup A K L Q E := by
  let I_E : GrpCat.{w} := actualFiniteStageInertiaGroup A K L Q E
  let I_F : GrpCat.{w} := actualFiniteStageInertiaGroup A K L Q F
  let P_E : Subgroup I_E.carrier := actualFiniteWildSubgroup A K L Q E
  let P_F : Subgroup I_F.carrier := actualFiniteWildSubgroup A K L Q F
  let rho : I_F.carrier →* I_E.carrier :=
    (actualFiniteInertiaTowerRestriction A K L Q E F hEF).hom'
  have onto : Function.Surjective rho.toFun :=
    actualFiniteInertiaTowerRestriction_surjective A K L Q E F hEF
  have finiteSource : Finite I_F.carrier := actualFiniteStageInertiaGroup_finite A K L Q F
  have normalTarget : P_E.Normal := actualFiniteWildSubgroup_normal A K L Q E
  have cardSource : ∃ r : ℕ, Nat.card (Subtype P_F.carrier) = p ^ r :=
    actualFiniteWildSubgroup_card_exists_pow_of_baseResidue_charP A K L Q F p
  have cardTarget : ∃ r : ℕ, Nat.card (Subtype P_E.carrier) = p ^ r :=
    actualFiniteWildSubgroup_card_exists_pow_of_baseResidue_charP A K L Q E p
  have indexSource : ¬ p ∣ P_F.index :=
    actualFiniteWildSubgroup_index_not_dvd_of_baseResidue_charP A K L Q F p
  have indexTarget : ¬ p ∣ P_E.index :=
    actualFiniteWildSubgroup_index_not_dvd_of_baseResidue_charP A K L Q E p
  change P_F.map rho = P_E
  clear_value rho
  clear_value P_F
  clear_value P_E
  clear_value I_F
  clear_value I_E
  clear actualFiniteWildSubgroup_map_of_baseResidue_charP
  clear charA qMax Q hEF E F gKL tAKL aAL aKL frAK aAK fL L fK K vA dA rA A
  obtain ⟨r, hr⟩ := cardSource
  obtain ⟨s, hs⟩ := cardTarget
  have sourcePrimary : IsPGroup p P_F := IsPGroup.of_card hr
  have targetPrimary : IsPGroup p P_E := IsPGroup.of_card hs
  exact map_eq_of_isPGroup_of_index_not_dvd p rho onto P_F P_E
    sourcePrimary targetPrimary indexSource indexTarget

/-- In residue characteristic zero both actual wild subgroups are trivial,
so the same inertia restriction has exactly the actual wild image. -/
theorem actualFiniteWildSubgroup_map_of_baseResidue_charZero
    [CharZero (IsLocalRing.ResidueField A)] :
    (actualFiniteWildSubgroup A K L Q F).map
        (actualFiniteInertiaTowerRestriction A K L Q E F hEF).hom' =
      actualFiniteWildSubgroup A K L Q E := by
  rw [actualFiniteWildSubgroup_eq_bot_of_baseResidue_charZero A K L Q F,
    actualFiniteWildSubgroup_eq_bot_of_baseResidue_charZero A K L Q E]
  exact Subgroup.map_bot (actualFiniteInertiaTowerRestriction A K L Q E F hEF).hom'

/-- Actual finite inertia restriction maps the SAME intrinsic wild subgroup
onto the target wild subgroup in every residue characteristic. -/
theorem actualFiniteWildSubgroup_map :
    (actualFiniteWildSubgroup A K L Q F).map
        (actualFiniteInertiaTowerRestriction A K L Q E F hEF).hom' =
      actualFiniteWildSubgroup A K L Q E := by
  by_cases hchar : ringChar (IsLocalRing.ResidueField A) = 0
  · have hc : CharZero (IsLocalRing.ResidueField A) :=
      (CharP.ringChar_zero_iff_CharZero (R := IsLocalRing.ResidueField A)).mp hchar
    exact actualFiniteWildSubgroup_map_of_baseResidue_charZero A K L Q E F hEF
  · have hp : Fact (ringChar (IsLocalRing.ResidueField A)).Prime :=
      ⟨CharP.char_prime_of_ne_zero (IsLocalRing.ResidueField A) hchar⟩
    exact actualFiniteWildSubgroup_map_of_baseResidue_charP A K L Q E F hEF
      (ringChar (IsLocalRing.ResidueField A))

end EtaleFundamentalGroups.Inertia

end
