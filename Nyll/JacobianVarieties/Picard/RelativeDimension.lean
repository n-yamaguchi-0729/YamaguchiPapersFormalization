/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_geometricallyIntegral
import Nyll.AlgebraicCurves.Geometry.Deformation.smoothOfRelativeDimension_of_finrank_cotangentSpace_eq
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_twoAffineOpenCover_of_section
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Nyll.JacobianVarieties.Picard.CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic
import Nyll.JacobianVarieties.Picard.Existence

/-!
# Relative dimension of a pointed Picard scheme over a field

The represented group law and geometric connectedness give geometric integrality.
The cotangent calculation at the rational zero section then determines the smooth
relative dimension as the first-cohomology dimension on a two-affine cover.

This constructs a dimension witness for pointed curves over arbitrary fields. It does
not assert unpointed existence or identify this dimension with a separate genus API.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.RelPicard

/-- The relative dimension of a smooth proper geometrically connected Picard representation
is the dimension of first cohomology of the original curve on any two-affine cover. -/
theorem RepresentsRelSubPic.smoothOfRelativeDimension_finrank_H1
    {K : Type u} [Field K] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of K)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
    {D : RelativePic0Designation K c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (𝒱 : C.TwoAffineOpenCover) :
    SmoothOfRelativeDimension (Module.finrank K (𝒱.structureSheafSections c).H1)
      D.toBase := by
  have hA : AbelianSchemePropertyBundle K D.toBase :=
    { smooth := inferInstance
      proper := inferInstance
      connectedFibres := fun x => D.toBase.isConnected_preimage_singleton x
      hasGroupLaw := ⟨h.relativeGroupLaw (P := algEquivZeroGroupCut c ε)⟩ }
  have : GeometricallyIntegral D.toBase := hA.geometricallyIntegral
  have : IrreducibleSpace D.P :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton D.toBase
  exact AlgebraicGeometry.smoothOfRelativeDimension_of_finrank_cotangentSpace_eq
    D.toBase D.zeroSection D.zeroSection_toBase
    (Module.finrank K (𝒱.structureSheafSections c).H1)
    (h.finrank_cotangentSpace_eq_H1 𝒱)

/-- A pointed smooth proper geometrically integral curve over any field has a represented
Picard scheme with its smooth relative dimension computed by first cohomology. Both the
representing scheme and the two-affine cover are constructed from the original curve. -/
theorem exists_representsRelSubPic_of_field_with_dimension (K : Type u) [Field K]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    ∃ (D : RelativePic0Designation K c) (𝒱 : C.TwoAffineOpenCover),
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧
          SmoothOfRelativeDimension (Module.finrank K (𝒱.structureSheafSections c).H1)
            D.toBase := by
  obtain ⟨D, ⟨h⟩, hs, hp, hg⟩ := exists_representsRelSubPic_of_field K c ε
  obtain ⟨𝒱, -, -⟩ := SmoothProperCurve.exists_twoAffineOpenCover_of_section K c ε
  have : Smooth D.toBase := hs
  have : IsProper D.toBase := hp
  have : GeometricallyConnected D.toBase := hg
  exact ⟨D, 𝒱, ⟨h⟩, hs, hp, hg, h.smoothOfRelativeDimension_finrank_H1 𝒱⟩

end AlgebraicGeometry.RelPicard
