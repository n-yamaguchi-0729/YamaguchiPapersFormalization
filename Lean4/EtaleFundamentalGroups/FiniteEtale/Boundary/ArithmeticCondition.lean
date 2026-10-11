/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.GaloisCategory
import SchemeTheory.Divisors.ArithmeticBoundary

/-!
# Galois-cover arithmetic boundary conditions

This module owns the boundary conditions whose statements quantify over
finite étale Galois covers.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace Scheme

namespace EffectiveCartierDivisor

variable {X S : Scheme.{u}}

/-- After every connected finite etale Galois cover, every irreducible
component of the pulled-back divisor has geometrically integral generic
fibre over the chosen integral base. -/
def HasGeometricallyIntegralGenericComponentsAfterGaloisCovers
    [IsIntegral X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S) : Prop :=
  ∀ (Y : FiniteEtale X), CategoryTheory.PreGaloisCategory.IsGalois Y →
    ∀ (Z : Set (D.1.comap Y.hom).subscheme)
      (hZ : Z ∈ irreducibleComponents (D.1.comap Y.hom).subscheme),
      GeometricallyIntegral
        ((D.pulledBackComponentToBase p Y Z hZ).fiberToSpecResidueField
          (genericPoint S))

/-- An arithmetic normal-crossings boundary condition at residue
characteristic `2`.

The ambient scheme is integral, normal and locally Noetherian.  The
conjunction explicitly contains reducedness and horizontality of the divisor,
regularity along its support, a characteristic `2` normal-crossing point on
every irreducible component, and geometric integrality of every generic
boundary component after each connected finite etale Galois cover. -/
def SatisfiesResidueCharacteristicTwoBoundaryCondition
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S) : Prop :=
  D.IsReduced ∧
    D.IsHorizontalOver p ∧
      D.IsAmbientRegularAlongSupport ∧
        D.HasNormalCrossingPointOfResidueCharacteristicOnEachComponent 2 ∧
          D.HasGeometricallyIntegralGenericComponentsAfterGaloisCovers p

/-- The residue-characteristic-two boundary condition over the integer base.

The structure morphism is not additional data: `Spec ℤ` is terminal in the
category of schemes.  `ULift` only places the integer base in the universe of
`X`. -/
def SatisfiesResidueCharacteristicTwoBoundaryConditionOverIntegers
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X) : Prop :=
  by
    letI : IsDomain (ULift.{u} ℤ) :=
      (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ
    exact D.SatisfiesResidueCharacteristicTwoBoundaryCondition
      (specULiftZIsTerminal.from X)


end EffectiveCartierDivisor

end Scheme

end AlgebraicGeometry
