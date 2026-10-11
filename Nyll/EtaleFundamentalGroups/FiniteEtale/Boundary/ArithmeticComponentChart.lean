/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ReducedIrreducibleComponentGeometry
import Nyll.EtaleFundamentalGroups.FiniteEtale.Boundary.GaloisStability
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral

/-!
# Local chart data at an arithmetic boundary component

The arithmetic boundary condition already supplies all point-free inputs at
the generic point of a component after a finite-etale Galois pullback.  This
file packages those inputs at the canonical component generic point: ambient
regularity, dominance over the arithmetic base, geometric integrality of the
generic fibre, and an affine principal Cartier chart.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

universe u

variable {X S : Scheme.{u}}

/-- Geometry and an affine principal chart at the canonical generic point of
a pulled-back arithmetic boundary component.  Neither the point nor the chart
is supplied as an additional hypothesis. -/
theorem galoisPullback_componentGenericPoint_chart
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryCondition p)
    (Y : FiniteEtale X) (hY : CategoryTheory.PreGaloisCategory.IsGalois Y)
    (Z : Set (D.1.comap Y.hom).subscheme)
    (hZ : Z ∈ irreducibleComponents (D.1.comap Y.hom).subscheme) :
    let I : Y.left.IdealSheafData := D.1.comap Y.hom
    let C := I.subscheme.reducedIrreducibleComponent Z hZ
    let x := I.componentGenericPoint Z hZ
    Y.left.IsRegularAt x ∧
      Order.coheight x = 1 ∧
        I.componentToBase (Y.hom ≫ p) Z hZ (genericPoint C) = genericPoint S ∧
          GeometricallyIntegral
            ((I.componentToBase (Y.hom ≫ p) Z hZ).fiberToSpecResidueField
              (genericPoint S)) ∧
            ∃ (U : Y.left.affineOpens) (_hx : x ∈ U.1) (f : Γ(Y.left, U.1)),
              IsRegular f ∧ I.ideal U = Ideal.span {f} := by
  let : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
  let : IsIntegral Y.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
  let : IsLocallyNoetherian Y.left :=
    EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale Y
  let D' : EffectiveCartierDivisor Y.left := D.comapFiniteEtale Y
  have hstable := D.galoisPullback_stability p hD Y hY
  dsimp only at hstable
  let I : Y.left.IdealSheafData := D.1.comap Y.hom
  let C := I.subscheme.reducedIrreducibleComponent Z hZ
  let x := I.componentGenericPoint Z hZ
  change Y.left.IsRegularAt x ∧
    Order.coheight x = 1 ∧
      I.componentToBase (Y.hom ≫ p) Z hZ (genericPoint C) = genericPoint S ∧
        GeometricallyIntegral
          ((I.componentToBase (Y.hom ≫ p) Z hZ).fiberToSpecResidueField
            (genericPoint S)) ∧
          ∃ (U : Y.left.affineOpens) (_hx : x ∈ U.1) (f : Γ(Y.left, U.1)),
            IsRegular f ∧ I.ideal U = Ideal.span {f}
  rcases hstable with ⟨_reduced, hhorizontal, hregular, hcomponents⟩
  refine ⟨hregular.isRegularAt_componentGenericPoint Z hZ,
    D'.2.coheight_componentGenericPoint_eq_one Z hZ, ?_,
      (hcomponents Z hZ).1, ?_⟩
  · exact I.componentToBase_genericPoint (Y.hom ≫ p) Z hZ
      (hhorizontal Z hZ)
  · exact D'.2.exists_affineChart_at_componentGenericPoint Z hZ

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
