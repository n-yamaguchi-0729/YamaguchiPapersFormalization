/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.Boundary.ArithmeticCondition
import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale

/-!
# Arithmetic-boundary conclusions for Galois pullbacks

The declarations in this module are the categorical Galois-cover layer over
the general finite étale divisor lemmas in SchemeTheory.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace Scheme

namespace EffectiveCartierDivisor

variable {X Y S : Scheme.{u}}

/-- The regularity and geometric-integrality conclusions of finite-etale
boundary stability.  Both are obtained from the stated boundary condition:
regularity ascends etale-locally, while geometric integrality is clause (ii)
evaluated on the given Galois cover. -/
lemma regularAlong_and_geometricallyIntegralGenericComponents_of_galoisPullback
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryCondition p)
    (Y' : FiniteEtale X) (hY' : CategoryTheory.PreGaloisCategory.IsGalois Y') :
    (D.1.comap Y'.hom).IsAmbientRegularAlongSupport ∧
      ∀ (Z : Set (D.1.comap Y'.hom).subscheme)
        (hZ : Z ∈ irreducibleComponents (D.1.comap Y'.hom).subscheme),
        GeometricallyIntegral
          ((D.pulledBackComponentToBase p Y' Z hZ).fiberToSpecResidueField
            (genericPoint S)) := by
  let hfiniteEtale : IsFiniteEtale Y'.hom := Y'.prop
  constructor
  · exact @IdealSheafData.IsAmbientRegularAlongSupport.comap_of_etale
      X Y'.left D.1 Y'.hom hfiniteEtale.toEtale hD.2.2.1
  · exact hD.2.2.2.2 Y' hY'

/-- For a connected finite-etale Galois pullback, the ambient scheme is
regular along the pulled-back boundary, and every pulled-back component has
geometrically integral generic fibre together with a residue-characteristic
two point where the pulled-back boundary has normal crossings. -/
lemma galoisPullback_regularAlong_and_componentConclusions
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryCondition p)
    (Y' : FiniteEtale X) (hY' : CategoryTheory.PreGaloisCategory.IsGalois Y') :
    (D.1.comap Y'.hom).IsAmbientRegularAlongSupport ∧
      ∀ (Z : Set (D.1.comap Y'.hom).subscheme)
        (hZ : Z ∈ irreducibleComponents (D.1.comap Y'.hom).subscheme),
        GeometricallyIntegral
            ((D.pulledBackComponentToBase p Y' Z hZ).fiberToSpecResidueField
              (genericPoint S)) ∧
          ∃ y : (D.1.comap Y'.hom).subscheme,
            y ∈ Z ∧
              ringChar (Y'.left.residueField
                ((D.1.comap Y'.hom).subschemeι y)) = 2 ∧
                (D.1.comap Y'.hom).IsNormalCrossingsAt
                  ((D.1.comap Y'.hom).subschemeι y) := by
  let hfiniteEtale : IsFiniteEtale Y'.hom := Y'.prop
  obtain ⟨hregular, hintegral⟩ :=
    D.regularAlong_and_geometricallyIntegralGenericComponents_of_galoisPullback
      p hD Y' hY'
  refine ⟨hregular, fun Z hZ ↦ ⟨hintegral Z hZ, ?_⟩⟩
  exact @exists_normalCrossingPointOfResidueCharacteristic_on_comapComponent
    X Y'.left D Y'.hom hfiniteEtale 2 hD.2.2.2.1 Z hZ

/-- Integer-base specialization of the finite-etale Galois pullback
conclusions.  The structure morphism is the canonical map to the terminal
scheme `Spec ℤ`, rather than additional input data. -/
lemma galoisPullback_regularAlong_and_componentConclusions_overIntegers
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryConditionOverIntegers)
    (Y' : FiniteEtale X) (hY' : CategoryTheory.PreGaloisCategory.IsGalois Y') :
    letI : IsDomain (ULift.{u} ℤ) :=
      (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ
    (D.1.comap Y'.hom).IsAmbientRegularAlongSupport ∧
      ∀ (Z : Set (D.1.comap Y'.hom).subscheme)
        (hZ : Z ∈ irreducibleComponents (D.1.comap Y'.hom).subscheme),
        GeometricallyIntegral
            ((D.pulledBackComponentToBase
                (specULiftZIsTerminal.from X) Y' Z hZ).fiberToSpecResidueField
              (genericPoint (Spec (CommRingCat.of (ULift.{u} ℤ))))) ∧
          ∃ y : (D.1.comap Y'.hom).subscheme,
            y ∈ Z ∧
              ringChar (Y'.left.residueField
                ((D.1.comap Y'.hom).subschemeι y)) = 2 ∧
                (D.1.comap Y'.hom).IsNormalCrossingsAt
                  ((D.1.comap Y'.hom).subschemeι y) := by
  let : IsDomain (ULift.{u} ℤ) :=
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ
  apply galoisPullback_regularAlong_and_componentConclusions D
    (specULiftZIsTerminal.from X) _ Y' hY'
  exact hD


end EffectiveCartierDivisor

end Scheme

end AlgebraicGeometry
