/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Geometry.Curves.GeometricGenus
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_twoAffineOpenCover_of_section
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_geometricallyIntegral
import Nyll.JacobianVarieties.Picard.RelativeDimension
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Nyll.JacobianVarieties.Picard.Existence

/-!
# The dimension of a represented Jacobian equals the geometric genus

The genus here is fixed by the original curve and its actual geometric function
field, independently of the choice of point, affine cover, or Picard representation.
No assumption on the characteristic or algebraic closedness is imposed.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.RelPicard

/-- The represented Jacobian has the geometric genus of the original curve as its
smooth relative dimension. The affine cover is constructed from the given point. -/
theorem RepresentsRelSubPic.smoothOfRelativeDimension_geometricGenus
    {K : Type u} [Field K] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of K)}
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
    {D : RelativePic0Designation K c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase] :
    SmoothOfRelativeDimension (SmoothProperCurve.geometricGenus K c) D.toBase := by
  obtain ⟨𝒱, -, -⟩ := SmoothProperCurve.exists_twoAffineOpenCover_of_section K c ε
  rw [← SmoothProperCurve.finrank_H1_eq_geometricGenus K c 𝒱]
  exact h.smoothOfRelativeDimension_finrank_H1 𝒱

/-- Pointed Picard existence with dimension equal to the independently defined actual
genus, properness and geometric integrality over any field. -/
theorem exists_representsRelSubPic_of_field_with_genus (K : Type u) [Field K]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    ∃ D : RelativePic0Designation K c,
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        SmoothOfRelativeDimension (SmoothProperCurve.geometricGenus K c) D.toBase ∧
          IsProper D.toBase ∧ GeometricallyIntegral D.toBase := by
  obtain ⟨D, ⟨h⟩, hs, hp, hg⟩ := exists_representsRelSubPic_of_field K c ε
  have : Smooth D.toBase := hs
  have : IsProper D.toBase := hp
  have : GeometricallyConnected D.toBase := hg
  have hA : AbelianSchemePropertyBundle K D.toBase :=
    { smooth := hs
      proper := hp
      connectedFibres := fun x => D.toBase.isConnected_preimage_singleton x
      hasGroupLaw := ⟨h.relativeGroupLaw (P := algEquivZeroGroupCut c ε)⟩ }
  exact ⟨D, ⟨h⟩, h.smoothOfRelativeDimension_geometricGenus, hp,
    hA.geometricallyIntegral⟩

end AlgebraicGeometry.RelPicard
