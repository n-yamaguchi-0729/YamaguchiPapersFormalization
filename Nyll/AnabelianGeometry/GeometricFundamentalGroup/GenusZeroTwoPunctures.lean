/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.RationalTwoPuncturedChart
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.GenusZeroParameter
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_ord_X_sub_C
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_ord_placeInfty_X
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Models.CurveModel_exists_curveModel_iso_of_algEquiv
import Nyll.AlgebraicCurves.Models.CurveModel_exists_iso_comp_toBase_eq_placeOfPoint_congr_eq
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Coordinates matching two specified punctures

The genus-zero parameter with a prescribed simple zero and pole determines a rational-function
field isomorphism carrying zero and infinity to precisely those places. The actual curve-model
isomorphism therefore identifies their open complement with the Laurent polynomial chart.
No characteristic restriction is needed for this geometric identification.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped Polynomial

namespace AnabelianGeometry.GeometricFundamentalGroup

variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]

open Classical in
/-- A genus-zero coordinate can match both specified distinct places, as zero and infinity. -/
theorem exists_ratFunc_algEquiv_zero_infinity_of_genus_zero (hg : genusFF K F = 0)
    (v₀ vInfty : Place K F) (hne : v₀ ≠ vInfty) :
    ∃ e : RatFunc K ≃ₐ[K] F,
      Place.congrRingEquiv e.toRingEquiv (fun a => e.commutes a)
        (RationalFunctionField.placeOfPoint K 0) = v₀ ∧
      Place.congrRingEquiv e.toRingEquiv (fun a => e.commutes a)
        (RationalFunctionField.placeInfty K) = vInfty := by
  classical
  obtain ⟨t, _, htr, hgen, hord⟩ := exists_parameter_of_genus_zero hg v₀ vInfty hne
  let e : RatFunc K ≃ₐ[K] F := (RatFunc.algEquivOfTranscendental t htr).trans
    ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv)
  have heX : e RatFunc.X = t := by
    change ((RatFunc.algEquivOfTranscendental t htr) RatFunc.X : F) = t
    rw [RatFunc.algEquivOfTranscendental_X]
  have hzero : (RationalFunctionField.placeOfPoint K 0).ord (RatFunc.X : RatFunc K) = 1 := by
    have h := RationalFunctionField.ord_X_sub_C K 0 (RationalFunctionField.placeOfPoint K 0)
    rw [Polynomial.C_0, sub_zero, RatFunc.algebraMap_X, Finsupp.add_apply,
      Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (RationalFunctionField.placeOfPoint_ne_placeInfty K 0),
      add_zero] at h
    exact h
  refine ⟨e, ?_, ?_⟩
  · let u := Place.congrRingEquiv e.toRingEquiv (fun a => e.commutes a)
      (RationalFunctionField.placeOfPoint K 0)
    have hpos : u.ord t = 1 := by
      rw [← heX]
      exact (Place.ord_congrRingEquiv e.toRingEquiv (fun a => e.commutes a)
        (RationalFunctionField.placeOfPoint K 0) RatFunc.X).trans hzero
    by_contra huv
    rw [hord, ite_eq_right huv] at hpos
    split_ifs at hpos <;> omega
  · let u := Place.congrRingEquiv e.toRingEquiv (fun a => e.commutes a)
      (RationalFunctionField.placeInfty K)
    have hneg : u.ord t = -1 := by
      rw [← heX]
      exact (Place.ord_congrRingEquiv e.toRingEquiv (fun a => e.commutes a)
        (RationalFunctionField.placeInfty K) RatFunc.X).trans
          (RationalFunctionField.ord_placeInfty_X K)
    by_contra huv
    rw [hord, ite_eq_right huv] at hneg
    split_ifs at hneg <;> omega

/-- The complement of any two distinct closed points on a proper genus-zero curve model is
isomorphic as a scheme to the spectrum of the Laurent polynomial ring. -/
theorem nonempty_laurent_iso_of_genus_zero_complement_pair
    (M : CurveModel K F) (hg : genusFF K F = 0) (x y : closedPoints M.C) (hne : x ≠ y)
    (U : M.C.Opens) (hU : (U : Set M.C) = {x.1, y.1}ᶜ) :
    Nonempty (U.toScheme ≅ Spec (.of (LaurentPolynomial K))) := by
  classical
  obtain ⟨e, he₀, heInfty⟩ := exists_ratFunc_algEquiv_zero_infinity_of_genus_zero hg
    (M.placeOfPoint y) (M.placeOfPoint x) (fun h => hne (M.placeOfPoint_bijective.1 h).symm)
  obtain ⟨N, _, _⟩ := CurveModel.exists_curveModel_iso_of_algEquiv e.symm M
  obtain ⟨i, _, hplace⟩ :=
    CurveModel.exists_iso_comp_toBase_eq_placeOfPoint_congr_eq e N M
  let z : closedPoints N.C := N.placeEquiv.symm (RationalFunctionField.placeInfty K)
  let w : closedPoints N.C := N.placeEquiv.symm (RationalFunctionField.placeOfPoint K 0)
  have hz : i.hom.base z.1 = x.1 := by
    have hp := hplace z
    have hzplace : N.placeOfPoint z = RationalFunctionField.placeInfty K :=
      N.placeEquiv.apply_symm_apply _
    rw [hzplace, heInfty] at hp
    exact congrArg Subtype.val (M.placeOfPoint_bijective.1 hp)
  have hw : i.hom.base w.1 = y.1 := by
    have hp := hplace w
    have hwplace : N.placeOfPoint w = RationalFunctionField.placeOfPoint K 0 :=
      N.placeEquiv.apply_symm_apply _
    rw [hwplace, he₀] at hp
    exact congrArg Subtype.val (M.placeOfPoint_bijective.1 hp)
  let V : N.C.Opens := i.hom ⁻¹ᵁ U
  have hV : (V : Set N.C) = {z.1, w.1}ᶜ := by
    apply Set.ext
    intro a
    change i.hom.base a ∈ (U : Set M.C) ↔ a ∉ {z.1, w.1}
    rw [hU, ← hz, ← hw]
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact not_congr (or_congr (Scheme.homeoOfIso i).injective.eq_iff
      (Scheme.homeoOfIso i).injective.eq_iff)
  obtain ⟨j⟩ := nonempty_laurent_iso_of_complement_zero_infinity N V hV
  exact ⟨(i.hom.preimageIso U).symm ≪≫ j⟩

end AnabelianGeometry.GeometricFundamentalGroup
