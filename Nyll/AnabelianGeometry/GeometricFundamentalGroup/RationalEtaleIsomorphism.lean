/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.RationalEtaleFunctionField
import Nyll.AlgebraicCurves.Models.CurveModel_exists_iso_comp_toBase_eq_placeOfPoint_congr_eq
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Finite etale covers of proper rational curve models

In characteristic zero, a finite etale surjection from an integral curve model to a
proper rational curve model is itself an isomorphism. The function-field equivalence
constructs a model isomorphism. Its action on valuation subrings agrees with restriction
along the original field map, so the two scheme morphisms agree on every closed point.
Geometric-point density on the reduced source then identifies the actual morphisms.

No fundamental-group presentation is used. Passing from arbitrary connected finite
etale covers to curve models and identifying the fundamental group are separate steps.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve

namespace AnabelianGeometry.GeometricFundamentalGroup

open AlgebraicCurves.Geometry.Schemes.Proofs
open SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat

open RigKerGeomPoints renaming ext_of_forall_geometric_point → geometricHomExt in
/-- Every finite etale surjection between integral proper curve models with rational
target over an algebraically closed field of characteristic zero is an isomorphism. -/
theorem isIso_of_finite_etale_rational
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field F]
    [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (M : CurveModel K (RatFunc K)) (N : CurveModel K F)
    (π : N.C ⟶ M.C) (hπ : π ≫ M.toBase = N.toBase)
    [IsFinite π] [Etale π] (hsurj : Function.Surjective π.base) : IsIso π := by
  obtain ⟨e, hint, hpoints⟩ :=
    exists_functionFieldEquiv_of_finite_etale_rational M N π hπ hsurj
  obtain ⟨i, hi, hip⟩ :=
    CurveModel.exists_iso_comp_toBase_eq_placeOfPoint_congr_eq e.symm N M
  have hrestrict (w : Place K F) :
      Place.congrRingEquiv e.symm.toRingEquiv (fun a => e.symm.commutes a) w =
        w.restrictAlong e.toAlgHom hint := by
    apply Place.ext
    rw [Place.congrRingEquiv_toValuationSubring]
    ext z
    rw [ValuationSubring.mem_comap]
    rfl
  have hpoint (y : {p : Spec (CommRingCat.of K) ⟶ N.C // p ≫ N.toBase = 𝟙 _}) :
      y.1 ≫ i.hom = y.1 ≫ π := by
    let q : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _} :=
      ⟨y.1 ≫ i.hom, by rw [Category.assoc, hi]; exact y.2⟩
    have hclosed : IsClosed
        ({i.hom.base (pointEquivClosedPoint N.toBase y).1} : Set M.C) := by
      rw [← Set.image_singleton]
      exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso i)).isClosedMap _
        (pointEquivClosedPoint N.toBase y).2
    have hplace :
        M.placeOfPoint ⟨i.hom.base (pointEquivClosedPoint N.toBase y).1, hclosed⟩ =
          Place.congrRingEquiv e.symm.toRingEquiv (fun a => e.symm.commutes a)
            (N.placeOfPoint (pointEquivClosedPoint N.toBase y)) :=
      hip (pointEquivClosedPoint N.toBase y)
    have hcp : pointEquivClosedPoint M.toBase q =
        ⟨i.hom.base (pointEquivClosedPoint N.toBase y).1, hclosed⟩ := by
      apply Subtype.ext
      simp only [pointEquivClosedPoint_apply_coe]
      exact Scheme.Hom.comp_apply y.1 i.hom (IsLocalRing.closedPoint K)
    have hq : M.pointEquivPlace q =
        (N.pointEquivPlace y).restrictAlong e.toAlgHom hint := by
      rw [CurveModel.pointEquivPlace_apply, hcp, hplace, hrestrict,
        ← CurveModel.pointEquivPlace_apply]
    have hq' := congrArg (fun w => (M.pointEquivPlace.symm w).1) hq
    rw [Equiv.symm_apply_apply, hpoints, Equiv.symm_apply_apply] at hq'
    exact hq'
  have hmap : i.hom = π := by
    apply geometricHomExt (R := K) (L := K) (Function.injective_id)
      N.toBase M.toBase i.hom π hi hπ
    intro y hy
    have hyid : y ≫ N.toBase = 𝟙 _ := by
      simpa only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id] using hy
    exact hpoint ⟨y, hyid⟩
  rw [← hmap]
  infer_instance

end AnabelianGeometry.GeometricFundamentalGroup
