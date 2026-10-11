/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26SolvableCoverings.Geometry.Boundary
import Nyll.Yamaguchi26SolvableCoverings.Theorem2Dot2BoundaryCondition
import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Nyll.SchemeTheory.Divisors.CartierEtale
import Nyll.SchemeTheory.Divisors.EtaleRegularity
import Nyll.SchemeTheory.Divisors.HorizontalEtale

/-!
# Lemma 2.4: stability under finite etale covers

Pulling a horizontal effective Cartier divisor satisfying condition `(†)` back along
a connected finite etale cover preserves horizontality and condition `(†)`.

Finite flat maps take the generic point of a component to a generic point, and
finiteness makes the map of components surjective. This supplies a point in residue
characteristic two upstairs. Regularity and normal crossings are preserved by etale
base change. The generic-fiber condition follows by composing finite etale covers.

Source: [Yamaguchi, arXiv:2610.02948v1](https://arxiv.org/abs/2610.02948v1), Lemma 2.4.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale

namespace Yamaguchi26SolvableCoverings

variable {X : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]

omit [ConnectedSpace X] [IsLocallyNoetherian X] in
/-- 補題 2.4：連結有限 étale 被覆への引き戻しは、
水平性と定義 2.2 の境界条件 `(†)` を保つ。 -/
theorem finite_etale_stability_2_4
    (D : X.EffectiveCartierDivisor) (hhor : IsHorizontal D)
    (hD : BoundaryCondition D) (Y : FiniteEtale X) (_hY : ConnectedSpace Y.left) :
    IsHorizontal (D.comapFiniteEtale Y) ∧ BoundaryCondition (D.comapFiniteEtale Y) := by
  obtain ⟨hregular, hcrossing, hgeneric⟩ := hD
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hbase : Y.hom ≫ toIntegers X = toIntegers Y.left :=
      specZIsTerminal.comp_from Y.hom
    change (D.comapFiniteEtale Y).IsHorizontalOver (toIntegers Y.left)
    rw [← hbase]
    exact D.comap_components_denseRange_of_isHorizontalOver
      (toIntegers X) Y.hom hhor
  · exact Scheme.IdealSheafData.IsAmbientRegularAlongSupport.comap_of_etale
      D.1 Y.hom hregular
  · exact D.exists_normalCrossingPointOfResidueCharacteristic_on_comapComponent
      Y.hom 2 hcrossing
  · intro Z hZ
    change HasGeometricallyIntegralGenericComponents
      ((D.1.comap Y.hom).comap Z.hom)
    rw [← D.1.comap_comp Z.hom Y.hom]
    exact hgeneric (FiniteEtale.mk (Z.hom ≫ Y.hom)) hZ

end Yamaguchi26SolvableCoverings
