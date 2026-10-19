/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.ConnectedSource
import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.SmoothFiniteSchemeConstants
import Nyll.SchemeTheory.FunctionFields.ArithmeticGeometricIntegrality
import Nyll.SchemeTheory.LocalGeometry.ConnectedDomainStalks
import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry
import Nyll.SchemeTheory.LocalGeometry.SmoothStalks

/-!
# Connected finite étale covers of smooth arithmetic schemes

The arithmetic constant-field theorem, applied to the actual finite étale
cover, gives geometric integrality of its generic fiber. All connectedness,
integrality, normality and characteristic-zero inputs are constructed here
from smoothness and the given geometric connectedness of the base generic fiber.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace EtaleFundamentalGroups

/-- A connected finite étale cover of a smooth surjective finite-type
arithmetic scheme with geometrically connected generic fiber has geometrically
integral generic fiber. -/
theorem geometricallyIntegral_genericFiber_of_connected_finiteEtale_over_smooth_integers
    {E : Scheme} (p : E ⟶ Spec (CommRingCat.of ℤ))
    [Smooth p] [QuasiCompact p] [Surjective p]
    [GeometricallyConnected
      (p.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of ℤ))))]
    (T : FiniteEtale E) [ConnectedSpace T.left] :
    GeometricallyIntegral
      ((T.hom ≫ p).fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of ℤ)))) := by
  let : IsDomain Γ(Spec (CommRingCat.of ℤ), ⊤) :=
    Function.Injective.isDomain (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom.hom
      (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.injective
  let : IsIntegrallyClosed Γ(Spec (CommRingCat.of ℤ), ⊤) :=
    IsIntegrallyClosed.of_equiv
      (Scheme.ΓSpecIso (CommRingCat.of ℤ)).symm.commRingCatIsoToRingEquiv
  let : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian p
  let : ConnectedSpace E := p.connectedSpace_of_geometricallyConnected_genericFiber
  let : IsIntegral E := isIntegral_of_connected_of_isDomain_stalk E
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk p x).1)
  let f : T.left ⟶ E := T.hom
  let q : T.left ⟶ Spec (CommRingCat.of ℤ) := f ≫ p
  let : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian q
  let : IsIntegral T.left := isIntegral_of_connected_of_isDomain_stalk T.left
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk q x).1)
  let : IsNormalIntegral T.left := IsNormalIntegral.of_stalks T.left
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk q x).2)
  let : Surjective f := IsFiniteEtale.surjective f
  let : CharZero E.functionField := charZero_functionField_of_dominant_integers p
  let : CharZero T.left.functionField := charZero_functionField_of_dominant_integers q
  let : Smooth (p.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of ℤ)))) := by
    exact MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback p ((Spec (CommRingCat.of ℤ)).fromSpecResidueField
        (genericPoint (Spec (CommRingCat.of ℤ))))) (inferInstance : Smooth p)
  let : GeometricallyIntegral
      (p.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of ℤ)))) :=
    Smooth.geometricallyIntegral_of_geometricallyConnected _
  exact geometricallyIntegral_arithmeticGenericFiber_of_functionField_tensor_isField q
    (isField_tensor_algebraicClosure_of_smooth_finite_scheme_cover f p)

end EtaleFundamentalGroups
