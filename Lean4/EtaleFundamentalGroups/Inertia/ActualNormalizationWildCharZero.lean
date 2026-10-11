/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualNormalizationWildSubgroup
import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaSeparation
import EtaleFundamentalGroups.Inertia.ActualFiniteWildProperties
import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaRestriction
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Original wild inertia is trivial in residue characteristic zero

The finite principal-unit groups vanish by their actual arithmetic theorem.
The proved faithfulness of all actual restrictions then detects the identity
in the original inertia group.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- The actual finite wild condition becomes the identity before the
original subgroup-to-bottom interface is opened. -/
private theorem actualWild_restriction_eq_one_charZero
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
    [CharZero (IsLocalRing.ResidueField A)]
    (E : FiniteGaloisIntermediateField K L)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier)
    (hσ : σ ∈ actualNormalizationWildSubgroup A K L Q) :
    (actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ = 1 := by
  have hE := (mem_actualNormalizationWildSubgroup A K L Q σ).mp hσ E
  exact ((Subgroup.eq_bot_iff_forall (actualFiniteWildSubgroup A K L Q E)).mp
    (actualFiniteWildSubgroup_eq_bot_of_baseResidue_charZero A K L Q E))
    ((actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ) hE

/-- In characteristic zero of the original base residue field, the SAME
independently defined global wild subgroup is trivial. -/
theorem actualNormalizationWildSubgroup_eq_bot_of_baseResidue_charZero
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
    [CharZero (IsLocalRing.ResidueField A)] :
    actualNormalizationWildSubgroup A K L Q = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall (actualNormalizationWildSubgroup A K L Q)).mpr
  intro σ hσ
  apply actualFiniteInertiaRestriction_jointly_injective A K L Q σ 1
  intro E
  exact (actualWild_restriction_eq_one_charZero A K L Q E σ hσ).trans
    (actualFiniteInertiaRestriction A K L Q E).hom'.map_one.symm

end EtaleFundamentalGroups.Inertia
