/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.RationalPuncturedChart
import Nyll.AlgebraicCurves.Models.CurveModel_range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_deg_placeInfty
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# The actual two-puncture chart of a rational curve

The complements of zero and infinity are affine. Their intersection has its actual section
ring embedded in the function field, with image equal to the Laurent polynomial image.
This constructs the scheme isomorphism with the multiplicative group chart.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve

namespace AnabelianGeometry.GeometricFundamentalGroup

universe u

open AlgebraicCurves.Models.Proofs
open CurveModel_range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl
open AlgebraicCurve.S1c Classical in
/-- The complement of zero and infinity in a proper rational curve model is the spectrum of
the Laurent polynomial ring. The section-ring comparison and affineness are constructed. -/
theorem nonempty_laurent_iso_of_complement_zero_infinity
    {K : Type u} [Field K] [IsAlgClosed K] (M : CurveModel K (RatFunc K))
    (U : M.C.Opens)
    (hU : (U : Set M.C) =
      {(M.placeEquiv.symm (RationalFunctionField.placeInfty K)).1,
        (M.placeEquiv.symm (RationalFunctionField.placeOfPoint K 0)).1}ᶜ) :
    Nonempty (U.toScheme ≅ Spec (.of (LaurentPolynomial K))) := by
  classical
  let x : closedPoints M.C := M.placeEquiv.symm (RationalFunctionField.placeInfty K)
  let y : closedPoints M.C := M.placeEquiv.symm (RationalFunctionField.placeOfPoint K 0)
  let V : M.C.Opens := ⟨{x.1}ᶜ, x.2.isOpen_compl⟩
  let W : M.C.Opens := ⟨{y.1}ᶜ, y.2.isOpen_compl⟩
  have hV : IsAffineOpen V := isAffineOpen_complement_of_degree_one M x
    (by rw [← CurveModel.placeEquiv_apply, Equiv.apply_symm_apply]
        exact RationalFunctionField.deg_placeInfty K) V rfl
  have hW : IsAffineOpen W := isAffineOpen_complement_of_degree_one M y
    (by rw [← CurveModel.placeEquiv_apply, Equiv.apply_symm_apply]
        exact RationalFunctionField.deg_placeOfPoint K 0) W rfl
  have hUW : U = V ⊓ W := by
    apply SetLike.coe_injective
    rw [hU]
    ext z
    change z ∉ {x.1, y.1} ↔ z ∉ {x.1} ∧ z ∉ {y.1}
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  have hVW : IsAffineOpen (V ⊓ W) :=
    (isAffineHom_diagonal_iff (f := M.toBase)).mp inferInstance
      ⊤ (isAffineOpen_top _) V (by rw [Scheme.Hom.preimage_top]; exact le_top)
      W (by rw [Scheme.Hom.preimage_top]; exact le_top) hV hW
  have haff : IsAffineOpen U := hUW ▸ hVW
  have inhabited : Nonempty U := by
    refine ⟨⟨(M.placeEquiv.symm (RationalFunctionField.placeOfPoint K 1)).1, ?_⟩⟩
    rw [← SetLike.mem_coe, hU]
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro heq
      exact RationalFunctionField.placeOfPoint_ne_placeInfty K 1
        (M.placeEquiv.symm.injective (Subtype.ext heq))
    · intro heq
      exact one_ne_zero (RationalFunctionField.placeOfPoint_injective K
        (M.placeEquiv.symm.injective (Subtype.ext heq)))
  let f : Γ(M.C, U) →+* RatFunc K :=
    M.ffEquiv.symm.toRingHom.comp (algebraMap Γ(M.C, U) M.C.functionField)
  have hf : Function.Injective f :=
    M.ffEquiv.symm.injective.comp (M.C.germToFunctionField_injective U)
  have hr : f.range = (ι K).range := by
    rw [show f.range = _ from range_sections_eq_iInf K M U haff, ← iInf_ne_ne_eq K]
    refine iInf_congr fun v => ?_
    have hmem : (M.placeEquiv.symm v).1 ∈ U ↔
        v ≠ RationalFunctionField.placeInfty K ∧
          v ≠ RationalFunctionField.placeOfPoint K 0 := by
      rw [hUW, TopologicalSpace.Opens.mem_inf,
        coe_placeEquiv_symm_mem_iff_ne K M V _ rfl v,
        coe_placeEquiv_symm_mem_iff_ne K M W _ rfl v]
    rw [iInf_congr_Prop hmem (f₂ := fun _ => v.toValuationSubring.toSubring)
      (fun _ => rfl), iInf_and]
  let ef : Γ(M.C, U) ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun a b h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  let ep : LaurentPolynomial K ≃+* (ι K).range := RingEquiv.ofBijective (ι K).rangeRestrict
    ⟨fun a b h => ι_injective K (congrArg Subtype.val h), (ι K).rangeRestrict_surjective⟩
  let e : Γ(M.C, U) ≃+* LaurentPolynomial K :=
    (ef.trans (RingEquiv.subringCongr hr)).trans ep.symm
  exact ⟨haff.isoSpec ≪≫ Scheme.Spec.mapIso e.symm.toCommRingCatIso.op⟩

end AnabelianGeometry.GeometricFundamentalGroup
