/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.Localized.Cardinality
import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.FixedFields

/-!
# The inertia field of a normalization prime

The localized inertia subgroup at a height-one normalization prime determines
an actual intermediate field of the generic Galois extension.  In residue
characteristic zero, the degree from this fixed field to the total field is
the ramification index.  The usual tower formula then separates the total
generic degree into its unramified and ramified factors.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

variable {A : Type uA} {K : Type uK} {L : Type uL}
variable [CommRing A] [IsDomain A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- The fixed field of the inertia subgroup attached to a normalization prime
after localization at the corresponding base prime. -/
abbrev localizedNormalizationInertiaField
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    IntermediateField K L :=
  HilbertRamification.Dedekind.fixedFieldOfSubgroup Gal(L/K)
    (localizedNormalizationInertia (K := K) (L := L) P Q)

variable [IsRegularRing A]
variable [FiniteDimensional K L] [IsGalois K L]

/-- The extension above the localized inertia fixed field has degree equal to
the ramification index of the selected normalization prime. -/
theorem finrank_localizedNormalizationInertiaField_eq_ramificationIdx
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
    [CharZero (A ⧸ P)] :
    Module.finrank
        (localizedNormalizationInertiaField (K := K) (L := L) P Q) L =
      Q.ramificationIdx A := by
  calc
    Module.finrank
        (localizedNormalizationInertiaField (K := K) (L := L) P Q) L =
        Nat.card
          (localizedNormalizationInertia (K := K) (L := L) P Q) := by
      simpa only [localizedNormalizationInertiaField,
        HilbertRamification.Dedekind.fixedFieldOfSubgroup] using
        (IsGaloisGroup.finrank_fixedPoints_eq_card_subgroup
          (G := Gal(L/K)) (K := K) (L := L)
          (H := localizedNormalizationInertia (K := K) (L := L) P Q))
    _ = Q.ramificationIdx A :=
      localizedNormalizationInertia_card_eq_ramificationIdx
        (K := K) (L := L) P hP Q

/-- The generic degree factors as the degree of the inertia fixed field times
the ramification index. -/
theorem finrank_eq_finrank_localizedNormalizationInertiaField_mul_ramificationIdx
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
    [CharZero (A ⧸ P)] :
    Module.finrank K L =
      Module.finrank K
          (localizedNormalizationInertiaField (K := K) (L := L) P Q) *
        Q.ramificationIdx A := by
  calc
    Module.finrank K L =
        Module.finrank K
            (localizedNormalizationInertiaField (K := K) (L := L) P Q) *
          Module.finrank
            (localizedNormalizationInertiaField (K := K) (L := L) P Q) L :=
      (Module.finrank_mul_finrank K
        (localizedNormalizationInertiaField (K := K) (L := L) P Q) L).symm
    _ = Module.finrank K
          (localizedNormalizationInertiaField (K := K) (L := L) P Q) *
        Q.ramificationIdx A := by
      rw [finrank_localizedNormalizationInertiaField_eq_ramificationIdx
        (K := K) (L := L) P hP Q]

end EtaleFundamentalGroups

end
