/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.Integral
import EtaleFundamentalGroups.FiniteEtale.Boundary.GaloisGenericComponents
import EtaleFundamentalGroups.FiniteEtale.Boundary.GaloisStability

/-!
# Arithmetic boundary stability under Galois covers

The full residue-characteristic-two boundary condition is inherited by a
connected finite-etale Galois pullback.  In particular, the result includes
the geometric-integrality clause after every further connected Galois cover.
Only local Noetherianity is used.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

universe u

variable {X S : Scheme.{u}}

/-- A connected finite-etale Galois pullback preserves the complete
residue-characteristic-two arithmetic boundary condition. -/
theorem galoisPullback_satisfiesResidueCharacteristicTwoBoundaryCondition
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryCondition p)
    (Y : FiniteEtale X) (hY : CategoryTheory.PreGaloisCategory.IsGalois Y) :
    letI : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : IsNormalIntegral Y.left :=
      isNormalIntegral_left_of_isConnected_finiteEtale Y
    letI : IsLocallyNoetherian Y.left :=
      isLocallyNoetherian_left_finiteEtale Y
    let D' : EffectiveCartierDivisor Y.left := D.comapFiniteEtale Y
    D'.SatisfiesResidueCharacteristicTwoBoundaryCondition (Y.hom ≫ p) := by
  let : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : IsNormalIntegral Y.left :=
    isNormalIntegral_left_of_isConnected_finiteEtale Y
  let : IsLocallyNoetherian Y.left :=
    isLocallyNoetherian_left_finiteEtale Y
  let D' : EffectiveCartierDivisor Y.left := D.comapFiniteEtale Y
  have hstable := D.galoisPullback_stability p hD Y hY
  dsimp only at hstable
  rcases hstable with ⟨hreduced, hhorizontal, hregular, hcomponents⟩
  refine ⟨hreduced, hhorizontal, hregular, ?_, ?_⟩
  · intro Z hZ
    exact (hcomponents Z hZ).2
  · intro Zc hZc F hF
    let : CategoryTheory.PreGaloisCategory.IsGalois Zc := hZc
    change GeometricallyIntegral
      ((((D.1.comap Y.hom).comap Zc.hom).componentToBase
        (Zc.hom ≫ (Y.hom ≫ p)) F hF).fiberToSpecResidueField
          (genericPoint S))
    rw [← Category.assoc]
    exact D.geometricallyIntegralGenericComponents_after_galoisPullback
      p hD.2.2.2.2 Y hY Zc hZc F hF

section IntegerBase

local instance : IsDomain (ULift.{u} ℤ) :=
  (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ

/-- Integer-base specialization.  The structure morphism of the pullback is
the unique morphism to `Spec ℤ`, so no extra base morphism is assumed. -/
theorem galoisPullback_satisfiesResidueCharacteristicTwoBoundaryCondition_overIntegers
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryConditionOverIntegers)
    (Y : FiniteEtale X) (hY : CategoryTheory.PreGaloisCategory.IsGalois Y) :
    letI : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : IsNormalIntegral Y.left :=
      isNormalIntegral_left_of_isConnected_finiteEtale Y
    letI : IsLocallyNoetherian Y.left :=
      isLocallyNoetherian_left_finiteEtale Y
    let D' : EffectiveCartierDivisor Y.left := D.comapFiniteEtale Y
    D'.SatisfiesResidueCharacteristicTwoBoundaryConditionOverIntegers := by
  let : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : IsNormalIntegral Y.left :=
    isNormalIntegral_left_of_isConnected_finiteEtale Y
  let : IsLocallyNoetherian Y.left :=
    isLocallyNoetherian_left_finiteEtale Y
  let D' : EffectiveCartierDivisor Y.left := D.comapFiniteEtale Y
  let p : X ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    specULiftZIsTerminal.from X
  have hgeneral :=
    D.galoisPullback_satisfiesResidueCharacteristicTwoBoundaryCondition
      p hD Y hY
  dsimp only at hgeneral
  change D'.SatisfiesResidueCharacteristicTwoBoundaryCondition
    (specULiftZIsTerminal.from Y.left)
  have hp : Y.hom ≫ p = specULiftZIsTerminal.from Y.left :=
    specULiftZIsTerminal.hom_ext _ _
  rw [← hp]
  exact hgeneral

end IntegerBase

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor
