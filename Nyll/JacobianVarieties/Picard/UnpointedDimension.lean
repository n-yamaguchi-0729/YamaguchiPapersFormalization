/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Picard.GenusDimension
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricGenusBaseChange
import Nyll.AlgebraicCurves.Geometry.Curves.geometricallyIntegral_of_smooth_of_geometricallyConnected
import Nyll.AlgebraicCurves.Geometry.Schemes.SmoothRelativeDimension
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace

/-!
# Dimension and geometric integrality of the descended Jacobian

The same descended scheme is used throughout. Its locally constant smooth
dimension is compared, after the actual finite extension, with the dimension of
the represented Picard scheme. Comparison of affine smooth charts determines the
integer dimension, including over imperfect fields.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Picard.Unpointed

private theorem relativeDimension_eq_of_point
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] (x : X) (n m : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension m f] : n = m := by
  obtain ⟨U, hU, hxU, hn⟩ :=
    KwSmoothIrredRelDimConstantEngine.kw_exists_relDim_appLE_top_of_relDim f n x
  obtain ⟨V, hV, hxV, hm⟩ :=
    KwSmoothIrredRelDimConstantEngine.kw_exists_relDim_appLE_top_of_relDim f m x
  exact KwSmoothIrredRelDimConstantEngine.kw_relDim_eq_of_mem_both hU hV hn hm hxU hxV

/-- The actual descent of a local Picard representative has the original curve's
geometric genus as its smooth dimension and is geometrically integral. -/
theorem smoothOfRelativeDimension_geometricGenus_of_picardDescent
    (K : Type u) [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (L : Type u) [Field L] [Algebra K L] [Module.Finite K L]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) (baseChange K c L))
    {D : RelativePic0Designation L (baseChange K c L)}
    (h : RepresentsRelSubPic (baseChange K c L) ε (algEquivZeroCut (baseChange K c L) ε) D)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of K))
    [Smooth p] [IsProper p] [GeometricallyConnected p]
    (e : pullback p (specMap K L) ≅ D.P)
    (he : e.hom ≫ D.toBase = baseChange K p L) :
    SmoothOfRelativeDimension (geometricGenus K c) p ∧ GeometricallyIntegral p := by
  have hgi : GeometricallyIntegral p :=
    geometricallyIntegral_of_smooth_of_geometricallyConnected p
  have : ConnectedSpace P := GeometricallyConnected.connectedSpace_of_subsingleton p
  obtain ⟨n, hn⟩ := Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace p
  have : SmoothOfRelativeDimension n p := hn
  have hi : e.inv ≫ baseChange K p L = D.toBase := by
    rw [← he, Iso.inv_hom_id_assoc]
  have : Smooth D.toBase := by
    rw [← hi]
    infer_instance
  have : IsProper D.toBase := by
    rw [← hi]
    infer_instance
  have hres (Q : MorphismProperty Scheme.{u}) (hbc : Q.IsStableUnderBaseChange) :
      Q.RespectsIso := by
    apply MorphismProperty.RespectsIso.of_respects_arrow_iso
    intro f g j
    exact hbc.of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk j.inv.w))
  have : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{u}) :=
    hres (@GeometricallyConnected) (GeometricallyConnected.eq_geometrically ▸ inferInstance)
  have : GeometricallyConnected D.toBase := by
    rw [← hi]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@GeometricallyConnected) e.inv (baseChange K p L)).mpr inferInstance
  have hbc : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension n) :=
    hres (@SmoothOfRelativeDimension n) hbc
  have : SmoothOfRelativeDimension n (baseChange K p L) :=
    hbc.of_isPullback (IsPullback.of_hasPullback p (specMap K L)) hn
  have hnD : SmoothOfRelativeDimension n D.toBase := by
    rw [← hi]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@SmoothOfRelativeDimension n) e.inv (baseChange K p L)).mpr inferInstance
  have hgD : SmoothOfRelativeDimension (geometricGenus K c) D.toBase := by
    rw [← geometricGenus_baseChange_of_finite_of_section K c L ε]
    exact h.smoothOfRelativeDimension_geometricGenus
  have hng : n = geometricGenus K c :=
    relativeDimension_eq_of_point D.toBase
      (D.zeroSection (default : Spec (CommRingCat.of L))) n (geometricGenus K c)
  exact ⟨hng ▸ hn, hgi⟩

end JacobianVarieties.Picard.Unpointed
