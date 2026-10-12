/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.Designation
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Schemes.isReduced_of_smooth_of_field
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.SchemeTheory.Modules.Monoidal

/-!
# Equality of Abel–Jacobi maps from their actual geometric point classes

For one represented Picard functor, two morphisms classifying the line bundle
of each geometric point minus the basepoint agree on geometric points.
The smooth source is reduced, so geometric point density proves equality of
the original morphisms over the arbitrary ground field.

The two point-class hypotheses are supplied by the joint group-law and
Abel–Jacobi construction and retained by Abel–Jacobi homomorphism detection.
No equality of the candidate morphisms or comparison of Picard carriers is
assumed.
-/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.RelPicard

open AlgebraicCurves.Geometry.Schemes.Proofs
open SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat

open RigKerGeomPoints renaming ext_of_forall_geometric_point → geometricHomExt in
/-- Two actual Abel–Jacobi morphisms into the same Picard representation are equal
if they both classify point-minus-basepoint line bundles over one algebraically
closed extension of the ground field. -/
theorem abelJacobi_eq_of_geometric_point_class
    (K : Type u) [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    (D : RelativePic0Designation K c) [IsSeparated D.toBase]
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (φ ψ : SchemeHomOver c D.toBase) :
    let t : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    (∀ x : SchemeHomOver t c,
      Nonempty ((hD.poincare.pullbackAlong
          ⟨x.1 ≫ φ.1, (Category.assoc _ _ _).trans
            ((congrArg (x.1 ≫ ·) φ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule)) →
    (∀ x : SchemeHomOver t c,
      Nonempty ((hD.poincare.pullbackAlong
          ⟨x.1 ≫ ψ.1, (Category.assoc _ _ _).trans
            ((congrArg (x.1 ≫ ·) ψ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule)) →
    φ = ψ := by
  intro t hφ hψ
  have : IsReduced C := isReduced_of_smooth_of_field c
  apply Subtype.ext
  apply geometricHomExt (R := K) (L := Ω) (algebraMap K Ω).injective
    c D.toBase φ.1 ψ.1 φ.2 ψ.2
  intro x hx
  let z : SchemeHomOver t c := ⟨x, hx⟩
  obtain ⟨eφ⟩ := hφ z
  obtain ⟨eψ⟩ := hψ z
  have heq : NeronModelInfra.schemeHomOverComp z φ =
      NeronModelInfra.schemeHomOverComp z ψ :=
    hD.ext_of_iso t _ _ ⟨eφ ≪≫ eψ.symm⟩
  exact congrArg Subtype.val heq

end AlgebraicGeometry.RelPicard
