/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Statements adapted from LeanEval/AlgebraicGeometry/JacobianChallenge.lean:
https://github.com/leanprover/lean-eval/blob/38361be884302c7edce1908c4aef8296eb2cb27e/LeanEval/AlgebraicGeometry/JacobianChallenge.lean

Local constructions and proofs:
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.UnpointedJacobian
import Nyll.JacobianVarieties.Picard.UnpointedAbelJacobi
import Nyll.JacobianVarieties.Picard.UnpointedAlbanese
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLawGrpObj
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricGenus
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIrreducible_geometricallyConnected
import Nyll.AlgebraicCurves.Geometry.Curves.geometricallyIntegral_of_smooth_of_geometricallyConnected
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Jacobians of smooth proper curves in the over category

The Jacobian, its group object, and every Abel--Jacobi map use the same scheme
constructed by finite faithfully flat descent without a rational basepoint.
The genus is the geometric function-field genus, also identified with actual
structure-sheaf cohomology. These declarations implement all nine
statements of the algebraic-geometric Jacobian challenge.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.JacobianChallenge

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

local instance curveIntegral : GeometricallyIntegral C.hom := by
  have _ : GeometricallyConnected C.hom :=
    GeometricallyIrreducible.geometricallyConnected C.hom
  exact geometricallyIntegral_of_smooth_of_geometricallyConnected C.hom

/-- The geometric genus of a smooth proper curve. -/
def genus (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] : ℕ :=
  SmoothProperCurve.geometricGenus k C.hom

/-- The Jacobian over the original field, with no rational basepoint required. -/
def Jacobian (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    Over (Spec (CommRingCat.of k)) :=
  Over.mk (JacobianVarieties.Picard.Unpointed.toBase k C.hom)

namespace Jacobian

/-- The group object induced by tensor product on the fixed descended Jacobian. -/
instance instGrpObj : GrpObj (Jacobian C) :=
  (JacobianVarieties.Picard.Unpointed.groupLaw k C.hom).grpObjOverMk

/-- The Jacobian has smooth relative dimension equal to the geometric genus. -/
instance smoothOfRelativeDimension_genus :
    SmoothOfRelativeDimension (genus C) (Jacobian C).hom :=
  JacobianVarieties.Picard.Unpointed.smoothOfRelativeDimension k C.hom

/-- Properness of the fixed Jacobian over the original field. -/
instance instIsProper : IsProper (Jacobian C).hom :=
  JacobianVarieties.Picard.Unpointed.proper k C.hom

/-- Geometric irreducibility of the fixed Jacobian over the original field. -/
instance instGeometricallyIrreducible : GeometricallyIrreducible (Jacobian C).hom := by
  have _ : GeometricallyIntegral (Jacobian C).hom :=
    JacobianVarieties.Picard.Unpointed.geometricallyIntegral k C.hom
  infer_instance

/-- The actual point-minus-basepoint Abel--Jacobi morphism in the over category. -/
def ofCurve (P : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) : C ⟶ Jacobian C :=
  let ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) C.hom := ⟨P.left, Over.w P⟩
  let aj : SchemeHomOver C.hom (JacobianVarieties.Picard.Unpointed.toBase k C.hom) :=
    JacobianVarieties.Picard.Unpointed.abelJacobi C.hom ε
  Over.homMk aj.1 aj.2

/-- The specified rational basepoint maps to the identity of the same group object. -/
theorem comp_ofCurve (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) :
    P ≫ ofCurve P = η[Jacobian C] := by
  apply Over.OverMorphism.ext
  have hz := JacobianVarieties.Picard.Unpointed.abelJacobi_basepoint C.hom
    (⟨P.left, Over.w P⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) C.hom)
  have hunit := (JacobianVarieties.Picard.Unpointed.groupLaw k C.hom).grpObjOverMk_one_eq
  exact hz.trans (congrArg Subtype.val hunit).symm

/-- Every pointed morphism to an abelian variety factors uniquely through the
same Abel--Jacobi morphism and the fixed Jacobian, over the original field. -/
theorem exists_unique_ofCurve_comp
    {k : Type u} [Field k]
    (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    {A : Over (Spec (.of k))} [Smooth A.hom] [IsProper A.hom] [GrpObj A]
    [GeometricallyIrreducible A.hom] (f : C ⟶ A) (hf : P ≫ f = η[A]) :
    ∃! (g : Jacobian C ⟶ A), f = ofCurve P ≫ g := by
  have : GeometricallyConnected A.hom :=
    GeometricallyIrreducible.geometricallyConnected A.hom
  have : GeometricallyIntegral A.hom :=
    geometricallyIntegral_of_smooth_of_geometricallyConnected A.hom
  let ε : SchemeHomOver (𝟙 (Spec (.of k))) C.hom := ⟨P.left, Over.w P⟩
  let q : SchemeHomOver C.hom A.hom := ⟨f.left, Over.w f⟩
  let : GrpObj (Over.mk A.hom) := inferInstanceAs (GrpObj A)
  let G : RelativeGroupLaw k A.hom := relativeGroupLawOfGrpObj k A.hom
  have hq : NeronModelInfra.schemeHomOverComp ε q = G.one (𝟙 _) := by
    apply Subtype.ext
    change P.left ≫ f.left = (1 : Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk A.hom).left
    rw [← MonObj.one_eq_one]
    exact congrArg (fun h => h.left) hf
  obtain ⟨g, hg, hu⟩ :=
    JacobianVarieties.Picard.Unpointed.exists_unique_abelJacobi_factorization
      C.hom ε A.hom G q hq
  let g' : Jacobian C ⟶ A := Over.homMk g.1 g.2
  refine ⟨g', ?_, ?_⟩
  · apply Over.OverMorphism.ext
    exact hg.symm
  · intro h hh
    let h' : SchemeHomOver (JacobianVarieties.Picard.Unpointed.toBase k C.hom) A.hom :=
      ⟨h.left, Over.w h⟩
    have he : h' = g := hu h' (congrArg (fun e => e.left) hh).symm
    apply Over.OverMorphism.ext
    exact congrArg Subtype.val he

end Jacobian
end AlgebraicGeometry.JacobianChallenge
