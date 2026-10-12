/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.RationalEtaleIsomorphism
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed
import Nyll.SchemeTheory.LocalGeometry.ConnectedDomainStalks
import Nyll.SchemeTheory.LocalGeometry.SmoothStalkNormality
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Connected finite etale covers of a proper rational curve

A connected finite etale cover of a proper rational curve model is an isomorphism
in characteristic zero. No curve model, function field, surjectivity, or integrality
of the cover is assumed. Smoothness gives domain stalks and local Noetherianity;
connectedness then gives integrality. The actual curve-model construction supplies
the input for the rational-cover theorem.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve

namespace AnabelianGeometry.GeometricFundamentalGroup

/-- A connected finite etale cover of a proper rational curve over an algebraically
closed field of characteristic zero is an isomorphism. -/
theorem isIso_of_connected_finite_etale_rational
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (M : CurveModel K (RatFunc K)) {Y : Scheme.{0}} [ConnectedSpace Y]
    (π : Y ⟶ M.C) [IsFinite π] [Etale π] : IsIso π := by
  let c : Y ⟶ Spec (CommRingCat.of K) := π ≫ M.toBase
  have relativeSmooth : SmoothOfRelativeDimension 1 c :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (π ≫ M.toBase))
  have smooth : Smooth c := SmoothOfRelativeDimension.smooth (n := 1) (f := c)
  have domainBase : IsDomain Γ(Spec (CommRingCat.of K), ⊤) :=
    Function.Injective.isDomain (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective
  have normalBase : IsIntegrallyClosed Γ(Spec (CommRingCat.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have noetherian : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian c
  have integral : IsIntegral Y := isIntegral_of_connected_of_isDomain_stalk Y
    (fun y => (Smooth.isDomain_and_isIntegrallyClosed_stalk c y).1)
  have proper : IsProper c := inferInstanceAs (IsProper (π ≫ M.toBase))
  let fieldAlgebra : Algebra K Y.functionField := (baseToFunctionField c).toAlgebra
  obtain ⟨fieldCurve, fieldFiniteType, N, i, hi, -⟩ :=
    SmoothProperCurve.exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed K Y c
  have finiteEtale : IsFiniteEtale π := ⟨⟩
  have surjective : Surjective π := IsFiniteEtale.surjective π
  have surjectiveComp : Function.Surjective (i.hom ≫ π).base :=
    π.surjective.comp i.hom.surjective
  have isoComp : IsIso (i.hom ≫ π) :=
    isIso_of_finite_etale_rational M N (i.hom ≫ π)
      (by rw [Category.assoc]; exact hi) surjectiveComp
  exact IsIso.of_isIso_comp_left i.hom π

end AnabelianGeometry.GeometricFundamentalGroup
