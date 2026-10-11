/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.OriginalFiniteInertiaRestriction
import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaLocalization
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationCoefficientSquare
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Residue triviality of localized finite inertia

Shows that a coefficient map satisfying the inertia difference condition becomes residue-trivial
after localization, and applies this to the finite inertia action.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- Localization of a residue-trivial coefficient map is residue-trivial.
This is the coefficient argument used by individual inertia localization,
with no group or automorphism dictionary in its interface. -/
private theorem localRingHom_comp_residue_of_sub_mem
    (B : Type w) [CommRing B] (P : Ideal B) [P.IsPrime]
    (s : B →+* B) (hP : P = P.comap s)
    (hs : ∀ b : B, s.toFun b - b ∈ P) :
    (IsLocalRing.residue (Localization.AtPrime P)).comp
        (Localization.localRingHom P P s hP) =
      IsLocalRing.residue (Localization.AtPrime P) := by
  apply IsLocalization.ringHom_ext P.primeCompl
  apply RingHom.ext
  intro b
  let T := Localization.AtPrime P
  have hm : algebraMap B T (s.toFun b - b) ∈ IsLocalRing.maximalIdeal T :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff T P (s.toFun b - b)).mpr (hs b)
  have heq : IsLocalRing.residue T (algebraMap B T (s.toFun b)) =
      IsLocalRing.residue T (algebraMap B T b) := by
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub]
    exact hm
  exact (congrArg (IsLocalRing.residue T)
    (Localization.localRingHom_to_map P P s hP b)).trans heq

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L))

/-- The same actual localized coefficient action fixes its residue field.
The original inertia congruence supplies this fact; it is not an endpoint input. -/
theorem actualFiniteInertiaLocalRingHom_comp_residue [Q.IsPrime]
    (E : FiniteGaloisIntermediateField K L)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    (IsLocalRing.residue
        (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))).comp
        (actualFiniteInertiaLocalRingHom A K L Q E σ) =
      IsLocalRing.residue
        (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) := by
  let := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  exact localRingHom_comp_residue_of_sub_mem
    (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (actualFiniteNormalizationRestrictionRingHom A K L E
      (actualNormalizationInertiaElement A K L Q σ))
    (actualFiniteNormalizationRestrictionRingHom_prime A K L Q E σ)
    (originalInertia_finiteNormalization_difference A K L Q E σ)

end EtaleFundamentalGroups.Inertia

end
