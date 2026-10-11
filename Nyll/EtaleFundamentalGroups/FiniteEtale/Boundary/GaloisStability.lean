/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.CartierEtale
import Nyll.SchemeTheory.Divisors.HorizontalEtale
import Nyll.SchemeTheory.Divisors.ReducedEtale
import Nyll.EtaleFundamentalGroups.FiniteEtale.Boundary.GaloisPullbackConclusions

/-!
# Finite-etale stability of arithmetic boundary data

This file packages the ideal-sheaf base-change results as an effective
Cartier divisor and records all conclusions for a fixed connected finite
etale Galois cover.  The hypotheses use local Noetherianity; there is no
finite-type or Nagata assumption.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace Scheme.EffectiveCartierDivisor

variable {X S : Scheme.{u}}

/-- All boundary conclusions on a fixed connected finite-etale Galois
pullback: reducedness, horizontality, regularity along the boundary,
geometric integrality of every generic boundary component, and a
residue-characteristic-two normal-crossing point on every component. -/
theorem galoisPullback_stability
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryCondition p)
    (Y : FiniteEtale X) (hY : CategoryTheory.PreGaloisCategory.IsGalois Y) :
    let D' : EffectiveCartierDivisor Y.left := D.comapFiniteEtale Y
    D'.IsReduced ∧
      D'.IsHorizontalOver (Y.hom ≫ p) ∧
        D'.IsAmbientRegularAlongSupport ∧
          ∀ (Z : Set D'.1.subscheme)
            (hZ : Z ∈ irreducibleComponents D'.1.subscheme),
            GeometricallyIntegral
                ((D'.1.componentToBase (Y.hom ≫ p) Z hZ).fiberToSpecResidueField
                  (genericPoint S)) ∧
              ∃ y : D'.1.subscheme,
                y ∈ Z ∧
                  ringChar (Y.left.residueField (D'.1.subschemeι y)) = 2 ∧
                    D'.IsNormalCrossingsAt (D'.1.subschemeι y) := by
  let hfiniteEtale : IsFiniteEtale Y.hom := Y.prop
  let D' : EffectiveCartierDivisor Y.left := D.comapFiniteEtale Y
  have hreduced : D'.IsReduced := by
    change (D.1.comap Y.hom).IsReduced
    exact @IdealSheafData.IsReduced.comap_of_etale X Y.left D.1 hD.1 Y.hom
      hfiniteEtale.toEtale (inferInstance : IsLocallyNoetherian X)
  have hhorizontal : D'.IsHorizontalOver (Y.hom ≫ p) := by
    change ∀ (Z : Set (D.1.comap Y.hom).subscheme)
      (hZ : Z ∈ irreducibleComponents (D.1.comap Y.hom).subscheme),
      DenseRange ((D.1.comap Y.hom).componentToBase (Y.hom ≫ p) Z hZ)
    exact @comap_components_denseRange_of_isHorizontalOver X Y.left S
      D p Y.hom hfiniteEtale hD.2.1
  obtain ⟨hregular, hcomponents⟩ :=
    D.galoisPullback_regularAlong_and_componentConclusions p hD Y hY
  refine ⟨hreduced, hhorizontal, hregular, ?_⟩
  intro Z hZ
  exact hcomponents Z hZ

section IntegerBase

local instance : IsDomain (ULift.{u} ℤ) :=
  (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ

/-- Integer-base specialization of `galoisPullback_stability`.  The base
morphism is the unique morphism to `Spec ℤ`; it is not additional input. -/
theorem galoisPullback_stability_overIntegers
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryConditionOverIntegers)
    (Y : FiniteEtale X) (hY : CategoryTheory.PreGaloisCategory.IsGalois Y) :
    let p : X ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
      specULiftZIsTerminal.from X
    let D' : EffectiveCartierDivisor Y.left := D.comapFiniteEtale Y
    D'.IsReduced ∧
      D'.IsHorizontalOver (Y.hom ≫ p) ∧
        D'.IsAmbientRegularAlongSupport ∧
          ∀ (Z : Set D'.1.subscheme)
            (hZ : Z ∈ irreducibleComponents D'.1.subscheme),
            GeometricallyIntegral
                ((D'.1.componentToBase (Y.hom ≫ p) Z hZ).fiberToSpecResidueField
                  (genericPoint (Spec (CommRingCat.of (ULift.{u} ℤ))))) ∧
              ∃ y : D'.1.subscheme,
                y ∈ Z ∧
                  ringChar (Y.left.residueField (D'.1.subschemeι y)) = 2 ∧
                    D'.IsNormalCrossingsAt (D'.1.subschemeι y) := by
  apply galoisPullback_stability D (specULiftZIsTerminal.from X) _ Y hY
  exact hD

end IntegerBase

end Scheme.EffectiveCartierDivisor

end AlgebraicGeometry

end
