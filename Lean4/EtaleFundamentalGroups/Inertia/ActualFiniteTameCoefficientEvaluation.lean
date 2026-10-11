/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaRestriction
import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaLocalization
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationCoefficientSquare
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationResidueMap
import EtaleFundamentalGroups.Inertia.ActualFiniteLocalResidue
import EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinate
import EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import EtaleFundamentalGroups.Inertia.CommAlgCanonicalTameCompositeEvaluation
import EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
import EtaleFundamentalGroups.Inertia.FiniteNormalizationAutomorphisms
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Basic

/-!
# Coefficient evaluation of finite tame coordinates

Identifies the local ring map in the character composite with the finite inertia action and
evaluates the ambient coordinate through a uniformizer ratio.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

private theorem localRingHom_eq_of_coefficient_square
    (B : Type w) [CommRing B] (P : Ideal B) [P.IsPrime]
    (s : B →+* B) (hP : P = P.comap s)
    (j : Localization.AtPrime P →+* Localization.AtPrime P)
    (hj : j.comp (algebraMap B (Localization.AtPrime P)) =
      (algebraMap B (Localization.AtPrime P)).comp s) :
    j = Localization.localRingHom P P s hP := by
  apply IsLocalization.ringHom_ext P.primeCompl
  exact hj.trans (RingHom.ext fun b =>
    (Localization.localRingHom_to_map P P s hP b).symm)

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L))

/-- The coefficient map in the lower composite factorization is the SAME
actual local action: the two local RingHoms agree on every coefficient. -/
theorem actualFiniteInertiaCompositeLocalRingHom_eq [Q.IsPrime]
    (E : FiniteGaloisIntermediateField K L)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    commAlgInertiaCompositeLocalRingHom A (finiteAbsoluteNormalizationAlgebra A K L E)
        (finiteAbsoluteNormalizationPrime A K L Q E)
        (actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ =
      actualFiniteInertiaLocalRingHom A K L Q E σ := by
  let := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  exact localRingHom_eq_of_coefficient_square
    (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (actualFiniteNormalizationRestrictionRingHom A K L E
      (actualNormalizationInertiaElement A K L Q σ))
    (actualFiniteNormalizationRestrictionRingHom_prime A K L Q E σ)
    (commAlgInertiaCompositeLocalRingHom A (finiteAbsoluteNormalizationAlgebra A K L E)
      (finiteAbsoluteNormalizationPrime A K L Q E)
      (actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ)
    (commAlgInertiaCompositeLocalRingHom_comp_coefficient A
      (finiteAbsoluteNormalizationAlgebra A K L E)
      (finiteAbsoluteNormalizationPrime A K L Q E)
      (actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ)

/-- At any uniformizer, the SAME existing ambient tame coordinate is the
residue of an actual coefficient ratio raised to its original e/n exponent.
The witness and the local coefficient equation are constructed together. -/
theorem actualFiniteTameCoordinate_exists_coefficient
    [IsDomain A] [IsDiscreteValuationRing A] [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    ∀ (π : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)),
      Irreducible π →
      ∃ c : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E),
        IsUnit c ∧ π * c = (actualFiniteInertiaLocalRingHom A K L Q E σ).toFun π ∧
        (((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val).val =
          (actualFiniteLocalResidueMap A K L Q E).toFun c ^
            ((finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A /
              actualFiniteStageTameOrder A K L Q E) := by
  let := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  let := finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  let := finiteAbsoluteNormalizationAutomorphisms_finite A K L E
  intro π hπ
  change ∃ c : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E),
    IsUnit c ∧ π * c = (actualFiniteInertiaLocalRingHom A K L Q E σ).toFun π ∧
    commAlgCanonicalTameCompositeValue A (finiteAbsoluteNormalizationAlgebra A K L E)
      (finiteAbsoluteNormalizationPrime A K L Q E)
      (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)
      (actualFiniteInertiaRestriction A K L Q E).hom'.toFun
      (actualFiniteNormalizationResidueMap A K L Q E) σ =
        (actualFiniteLocalResidueMap A K L Q E).toFun c ^
          ((finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A /
            actualFiniteStageTameOrder A K L Q E)
  obtain ⟨c, hc, hπc, hvalue⟩ :=
    commAlgCanonicalTameCompositeValue_exists_coefficient A
      (finiteAbsoluteNormalizationAlgebra A K L E)
      (finiteAbsoluteNormalizationPrime A K L Q E)
      (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)
      (actualFiniteInertiaRestriction A K L Q E).hom'.toFun
      (actualFiniteNormalizationResidueMap A K L Q E) π hπ σ
  refine ⟨c, hc, ?_, ?_⟩
  · exact hπc.trans (congrArg
      (fun f : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E) →+*
          Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E) => f.toFun π)
      (actualFiniteInertiaCompositeLocalRingHom_eq A K L Q E σ))
  · have hi :
        (actualFiniteNormalizationResidueMap A K L Q E).toFun
            ((IsLocalRing.residue
              (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))).toFun c) =
          (actualFiniteLocalResidueMap A K L Q E).toFun c :=
      (congrArg
        (fun f : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E) →+*
            Q.ResidueField => f.toFun c)
        (actualFiniteLocalResidueMap_eq_residueMap_comp A K L Q E)).symm
    exact hvalue.trans (congrArg
      (fun x : Q.ResidueField => x ^
        ((finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A /
          actualFiniteStageTameOrder A K L Q E)) hi)

end EtaleFundamentalGroups.Inertia

end
