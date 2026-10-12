/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.SeparableAlbaneseChartGlue
import Nyll.JacobianVarieties.Albanese.GeometricPaddedDivisors
import Nyll.JacobianVarieties.Picard.Exists_abelJacobi_of_representsRelSubPic
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Schemes.isReduced_of_smooth_of_field
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Actual Abel--Jacobi factorization after a finite separable extension

Over the field extension constructed from the curve's chart sections, the glued
divisor sum factors every pointed morphism to a smooth proper geometrically
integral group scheme. The equality is checked on geometric points using actual
padded divisors, then geometric density gives equality of scheme morphisms.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra GoodReductionJacobian
open AlgebraicCurves.Geometry.Schemes.Proofs
open SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat

namespace JacobianVarieties.Albanese

open RigKerGeomPoints renaming ext_of_forall_geometric_point → geometricHomExt in
/-- A finite separable extension constructed from the pointed curve admits the
actual Abel--Jacobi factorization for every smooth proper geometrically integral
group target. The same morphism retains its full geometric point-class formula. -/
theorem exists_finite_separable_abelJacobi_factorization
    (K : Type u) [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
      (_ : Algebra.IsSeparable K L),
      let cL := SmoothProperCurve.baseChange K c L
      let εL := sectionBaseChange L ε
      ∀ (P : RelativePic0Designation L cL)
        [LocallyOfFiniteType P.toBase] [IsReduced P.P]
        (h : RepresentsRelSubPic cL εL (algEquivZeroCut cL εL) P),
        ∃ aj : SchemeHomOver cL P.toBase,
          εL.1 ≫ aj.1 = P.zeroSection ∧
          (∀ (F : Type u) [Field F]
            (s : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of L))
            (x : SchemeHomOver s cL),
            Nonempty ((h.poincare.pullbackAlong
              ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
                ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
              (RelEffCartierDiv.ofPoint cL x.1 x.2).lineBundle ⊗
                (RelEffCartierDiv.ofPoint cL (s ≫ εL.1)
                  ((Category.assoc _ _ _).trans
                    ((congrArg (s ≫ ·) εL.2).trans (Category.comp_id s)))).idealModule)) ∧
          ∀ (B : Scheme.{u}) (b : B ⟶ Spec (CommRingCat.of L)) [Smooth b] [IsProper b]
            [GeometricallyIntegral b] (G : RelativeGroupLaw L b) (q : SchemeHomOver cL b),
            NeronModelInfra.schemeHomOverComp εL q = G.one (𝟙 _) →
              ∃ ψ : SchemeHomOver P.toBase b, aj.1 ≫ ψ.1 = q.1 := by
  obtain ⟨L, hL, hKL, hfin, hsep, hglue⟩ := exists_finite_separable_divisorSum_glue K c ε
  refine ⟨L, hL, hKL, hfin, hsep, ?_⟩
  intro cL εL P _ _ h
  obtain ⟨aj, haj, hclass⟩ := exists_abelJacobi_of_representsRelSubPic L cL εL P h
  refine ⟨aj, haj, hclass, ?_⟩
  intro B b _ _ _ G q hq
  obtain ⟨r, hr, Y, y, U, hU, σ, hσ, sum, ψ, hI, hsum, hfield, _⟩ :=
    hglue P h B b G q
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have : IsReduced (pullback c (specMap K L)) := isReduced_of_smooth_of_field cL
  refine ⟨ψ, ?_⟩
  let s : Spec (CommRingCat.of (AlgebraicClosure L)) ⟶ Spec (CommRingCat.of L) :=
    specMap L (AlgebraicClosure L)
  apply geometricHomExt (R := L) (L := AlgebraicClosure L)
    (algebraMap L (AlgebraicClosure L)).injective cL b (aj.1 ≫ ψ.1) q.1
    (by rw [Category.assoc, ψ.2, aj.2]) q.2
  intro x hx
  let z : SchemeHomOver s cL := ⟨x, hx⟩
  obtain ⟨D, hD, ⟨eD⟩⟩ :=
    exists_padded_divisor_twist_iso_of_fieldMap cL εL (AlgebraicClosure L) s z n
  obtain ⟨eaj⟩ := hclass (AlgebraicClosure L) s z
  have hp := hfield (AlgebraicClosure L) s D
    ⟨x ≫ aj.1, by rw [Category.assoc, aj.2, hx]⟩ ⟨eD ≪≫ eaj.symm⟩
  rw [Category.assoc] at hp
  exact hp.trans (padded_divisor_sum_of_fieldMap cL εL (AlgebraicClosure L) s z n
    hU σ hσ hI G q hq sum hsum D hD)

end JacobianVarieties.Albanese
