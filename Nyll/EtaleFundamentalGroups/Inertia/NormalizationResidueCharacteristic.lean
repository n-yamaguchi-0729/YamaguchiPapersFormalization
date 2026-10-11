/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.NativeNormalizationPrime
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Base and normalization residue characteristic

The actual coefficient map descends from the base local ring to its residue
field at every prime lying over its maximal ideal. Its field-domain injectivity
identifies the two residue characteristics, including mixed-characteristic bases.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v

/-- The actual coefficient map on residue fields at a prime lying over
the closed point of the local base. -/
def baseResidueToIdealResidue
    (A : Type u) (B : Type v) [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B]
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal A)] :
    IsLocalRing.ResidueField A →+* Q.ResidueField :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal A)
    ((algebraMap B Q.ResidueField).comp (algebraMap A B)) (by
      intro a ha
      change algebraMap B Q.ResidueField (algebraMap A B a) = 0
      apply Ideal.algebraMap_residueField_eq_zero.mpr
      change a ∈ Q.under A
      rw [← Q.over_def (IsLocalRing.maximalIdeal A)]
      exact ha)

/-- The actual prime residue field has the same exponential characteristic
as the base residue field, through the injective coefficient residue map. -/
theorem idealResidue_ringExpChar_eq_baseResidue
    (A : Type u) (B : Type v) [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B]
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal A)] :
    ringExpChar Q.ResidueField = ringExpChar (IsLocalRing.ResidueField A) := by
  have hchar : CharP Q.ResidueField (ringChar (IsLocalRing.ResidueField A)) :=
    charP_of_injective_ringHom (f := baseResidueToIdealResidue A B Q)
      (baseResidueToIdealResidue A B Q).injective (ringChar (IsLocalRing.ResidueField A))
  exact congrArg (fun p : ℕ => max p 1)
    (ringChar.eq Q.ResidueField (ringChar (IsLocalRing.ResidueField A)))

/-- At an actual maximal normalization prime, the residue characteristic
is the base residue characteristic; its contraction is constructed. -/
theorem normalizationResidue_ringExpChar_eq_baseResidue
    (A : Type u) (F : Type v) [CommRing A] [IsLocalRing A]
    [CommRing F] [Algebra A F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal] :
    ringExpChar Q.ResidueField = ringExpChar (IsLocalRing.ResidueField A) := by
  have hover : Q.LiesOver (IsLocalRing.maximalIdeal A) :=
    normalizationCommAlgCat_liesOver_maximalIdeal Q
  exact idealResidue_ringExpChar_eq_baseResidue A (normalizationCommAlgCat A F) Q

end EtaleFundamentalGroups.Inertia

end
