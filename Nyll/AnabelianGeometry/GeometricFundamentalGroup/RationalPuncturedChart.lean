/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.CurveModel_exists_comp_toBase_eq_id_and_base_closedPoint_eq_of_deg_eq_one
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_finiteMapData_le_isUnit
import Nyll.AlgebraicCurves.Geometry.Curves.geometricallyIntegral_of_isAlgClosed
import Nyll.AlgebraicCurves.Models.CurveModel_range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl
import Nyll.AlgebraicCurves.Places.Rational.Classification
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_deg_placeInfty
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver

/-!
# The affine chart obtained by removing infinity

Affineness is obtained from the proved finite-coordinate construction for pointed proper curves.
The actual image of the section ring in the function field is then identified with the
intersection of the finite valuation rings, hence with the polynomial ring. Both steps are
proved for the given open subset, rather than supplied as comparison assumptions.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra
open scoped Polynomial

namespace AnabelianGeometry.GeometricFundamentalGroup

universe u

/-- The complement of a degree-one closed point on a smooth proper curve model is affine. -/
theorem isAffineOpen_complement_of_degree_one
    {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F) (x : closedPoints M.C) (hx : (M.placeOfPoint x).deg = 1)
    (U : M.C.Opens) (hU : (U : Set M.C) = {x.1}ᶜ) : IsAffineOpen U := by
  obtain ⟨pt, hpt, hpoint⟩ :=
    M.exists_comp_toBase_eq_id_and_base_closedPoint_eq_of_deg_eq_one x hx
  have geom : GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase
  let ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase := ⟨pt, hpt⟩
  obtain ⟨d, _, _⟩ := SmoothProperCurve.exists_finiteMapData_le_isUnit K M.toBase ε 0
  have hrange : Set.range pt.base = {x.1} := by
    apply Set.ext
    intro y
    constructor
    · rintro ⟨z, rfl⟩
      rw [Subsingleton.elim z (IsLocalRing.closedPoint K), hpoint]
      exact Set.mem_singleton _
    · intro hy
      exact ⟨IsLocalRing.closedPoint K, hpoint.trans (Set.mem_singleton_iff.mp hy).symm⟩
  have heq : U = d.U := by
    apply SetLike.coe_injective
    rw [hU, d.coe_U_eq_compl]
    change {x.1}ᶜ = (Set.range pt.base)ᶜ
    rw [hrange]
  rw [heq]
  exact d.isAffineOpen_U

open AlgebraicCurves.Models.Proofs
open CurveModel_range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl
open AlgebraicCurve.S1c Classical in
/-- Removing the point at infinity from any proper rational curve model gives the actual
affine line as a scheme. No affine-chart or coordinate-ring isomorphism is assumed. -/
theorem nonempty_affineLine_iso_of_complement_infinity
    {K : Type u} [Field K] [IsAlgClosed K] (M : CurveModel K (RatFunc K))
    (U : M.C.Opens)
    (hU : (U : Set M.C) = {(M.placeEquiv.symm (RationalFunctionField.placeInfty K)).1}ᶜ) :
    Nonempty (U.toScheme ≅ Spec (.of K[X])) := by
  classical
  have haff : IsAffineOpen U := isAffineOpen_complement_of_degree_one M _
    (by rw [← CurveModel.placeEquiv_apply, Equiv.apply_symm_apply]
        exact RationalFunctionField.deg_placeInfty K) U hU
  have inhabited : Nonempty U := by
    refine ⟨⟨(M.placeEquiv.symm (RationalFunctionField.placeOfPoint K 0)).1, ?_⟩⟩
    rw [← SetLike.mem_coe, hU, Set.mem_compl_singleton_iff]
    intro heq
    exact RationalFunctionField.placeOfPoint_ne_placeInfty K 0
      (M.placeEquiv.symm.injective (Subtype.ext heq))
  let f : Γ(M.C, U) →+* RatFunc K :=
    M.ffEquiv.symm.toRingHom.comp (algebraMap Γ(M.C, U) M.C.functionField)
  have hf : Function.Injective f :=
    M.ffEquiv.symm.injective.comp (M.C.germToFunctionField_injective U)
  have hr : f.range = (algebraMap K[X] (RatFunc K)).range := by
    rw [show f.range = _ from range_sections_eq_iInf K M U haff,
      ← map_polyPart_eq_range_algebraMap K, ← iInf_ne_placeInfty_eq K]
    exact iInf_congr fun v => iInf_congr_Prop
      (coe_placeEquiv_symm_mem_iff_ne K M U _ hU v) (fun _ => rfl)
  let ef : Γ(M.C, U) ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun a b h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  let p : K[X] →+* RatFunc K := algebraMap K[X] (RatFunc K)
  let ep : K[X] ≃+* p.range := RingEquiv.ofBijective p.rangeRestrict
    ⟨fun a b h => IsFractionRing.injective K[X] (RatFunc K) (congrArg Subtype.val h),
      p.rangeRestrict_surjective⟩
  let e : Γ(M.C, U) ≃+* K[X] := (ef.trans (RingEquiv.subringCongr hr)).trans ep.symm
  exact ⟨haff.isoSpec ≪≫ Scheme.Spec.mapIso e.symm.toCommRingCatIso.op⟩

end AnabelianGeometry.GeometricFundamentalGroup
