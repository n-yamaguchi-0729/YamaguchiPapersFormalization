/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.Coset.Card
import Nyll.EtaleFundamentalGroups.Inertia.Localized.Cardinality

/-!
# Divisibility of a Galois ramification index by the field degree

At a characteristic-zero height-one prime, the ramification index is the
order of the corresponding inertia subgroup.  Lagrange's theorem therefore
makes it divide the order of the full Galois group, which is the field
degree.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u v w

/--
For a finite Galois extension, every characteristic-zero height-one
ramification index divides the field degree.
-/
theorem normalization_ramificationIdx_dvd_finrank_of_charZero
    {A : Type u} {K : Type v} {L : Type w}
    [CommRing A] [IsDomain A] [IsRegularRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
    [CharZero (A ⧸ P)] :
    Q.ramificationIdx A ∣ Module.finrank K L := by
  have hdiv :
      Nat.card (localizedNormalizationInertia (K := K) (L := L) P Q) ∣
        Nat.card Gal(L/K) :=
    Subgroup.card_dvd_of_injective
      (localizedNormalizationInertia (K := K) (L := L) P Q).subtype
      (localizedNormalizationInertia (K := K) (L := L) P Q).subtype_injective
  rw [localizedNormalizationInertia_card_eq_ramificationIdx
      (K := K) (L := L) P hP Q,
    IsGalois.card_aut_eq_finrank] at hdiv
  exact hdiv

end EtaleFundamentalGroups
