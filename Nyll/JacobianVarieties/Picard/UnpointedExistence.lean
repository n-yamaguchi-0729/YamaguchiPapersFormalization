/-
Copyright (c) 2026 Naganori Yamaguchi.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.FiniteExtensionPoint
import Nyll.AlgebraicCurves.Geometry.Descent.FaithfullyFlatProperties
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_finiteMapData_le_isUnit
import Nyll.JacobianVarieties.Picard.Existence
import Nyll.JacobianVarieties.Picard.UnpointedDescent
import Nyll.JacobianVarieties.Picard.Exists_isAffineOpen_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData

/-!
# Existence of a smooth proper unpointed Picard descent

A closed point supplies a finite residue extension and an actual section of the
extended curve. Pointed Picard existence and its affine-neighborhood theorem apply
there. The unrigidified quotient presheaf supplies the descent action, and its effective
quotient gives a smooth proper geometrically connected scheme over the original field.

This statement retains the local representation and the actual descent compatibility.
Identifying the result with an fppf sheafification and descending its group law are
separate constructions.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Picard.Unpointed

/-- Every smooth proper geometrically integral curve over an arbitrary field has
a smooth proper geometrically connected descent of a pointed Picard representation.
The point and local representation are constructed, including in positive characteristic. -/
theorem exists_smooth_proper_picardDescent_of_field
    (K : Type u) [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
      (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) (baseChange K c L))
      (D : RelativePic0Designation L (baseChange K c L))
      (h : RepresentsRelSubPic (baseChange K c L) ε (algEquivZeroCut (baseChange K c L) ε) D)
      (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of K)),
      Smooth p ∧ IsProper p ∧ GeometricallyConnected p ∧
      ∃ (e : pullback p (specMap K L) ≅ D.P)
        (he : e.hom ≫ D.toBase = pullback.snd p (specMap K L)),
        DescentAction.eRel (specMap K L) D.toBase p e he ≫ (descentAction c L ε h).act =
          (DescentAction.canonical (specMap K L) p).act ≫ e.hom := by
  obtain ⟨x₀, -⟩ := c.surjective (default : Spec (CommRingCat.of K))
  have : Nonempty C := ⟨x₀⟩
  obtain ⟨x, -, hfin⟩ := Scheme.exists_finite_pointResidueAlgebra c
  let a : Algebra K (C.residueField x) := Scheme.pointResidueAlgebra c x
  have : Module.Finite K (C.residueField x) := hfin
  let ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (C.residueField x))))
      (baseChange K c (C.residueField x)) := Scheme.pointResidueSection c x
  obtain ⟨D, ⟨h⟩, hsm, hpr, hgc⟩ :=
    exists_representsRelSubPic_of_field (C.residueField x) (baseChange K c (C.residueField x)) ε
  have h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : FiniteMapData (baseChange K c (C.residueField x)) ε, m₀ ≤ 𝔉.m := by
    intro m₀
    obtain ⟨𝔉, hm, -⟩ := exists_finiteMapData_le_isUnit (C.residueField x)
      (baseChange K c (C.residueField x)) ε m₀
    exact ⟨𝔉, hm⟩
  have haff : ∀ S : Finset D.P, ∃ U : D.P.Opens, IsAffineOpen U ∧ ∀ y ∈ S, y ∈ U :=
    exists_isAffineOpen_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
      (C.residueField x) (baseChange K c (C.residueField x)) ε h𝔉 D h hsm hpr hgc
  obtain ⟨P, p, e, he, hc⟩ :=
    descentAction_effective_of_finite_fieldExtension c (C.residueField x) ε h haff
  obtain ⟨hs, hp, hg⟩ :=
    smooth_isProper_geometricallyConnected_of_faithfullyFlat_baseChange K (C.residueField x)
      p D.toBase hsm hpr hgc e he
  exact ⟨C.residueField x, inferInstance, a, inferInstance, ε, D, h, P, p,
    hs, hp, hg, e, he, hc⟩

end JacobianVarieties.Picard.Unpointed
