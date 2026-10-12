/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.IsClosed_singleton_of_ne_genericPoint
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Places.Place_exists_ord_eq_one
import Nyll.AlgebraicCurves.Places.Place_mem_of_ord_nonneg
import Nyll.JacobianVarieties.Kummer.OpenDivisorResidues
import Nyll.SchemeTheory.FunctionFields.StalkFunctoriality

/-!
# Local Kummer equations away from a boundary

Only the valuation at the point in question is used to remove an nth
power and obtain a unit. For an actual open immersion, the canonical
function-field map transports these two local-ring membership statements.
No comparison with the cohomology of the open curve is postulated.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicCurve.CurveModel

universe u v

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]

private theorem ord_pow (v : Place K F) (a : F) (n : ℕ) :
    v.ord (a ^ n) = (n : ℤ) * v.ord a := by
  rw [← zpow_natCast, v.ord_zpow]

private theorem ffEquiv_mem_stalk_range (M : CurveModel K F) (x : closedPoints M.C)
    (a : F) (ha : a ∈ (M.placeOfPoint x).toValuationSubring) :
    M.ffEquiv a ∈ (algebraMap (M.C.presheaf.stalk x.val) M.C.functionField).range := by
  change a ∈ (M.placeOfPoint x).toValuationSubring.toSubring at ha
  rw [← M.range_stalk_eq x] at ha
  obtain ⟨b, hb⟩ := ha
  refine ⟨b, M.ffEquiv.symm.injective ?_⟩
  rw [RingEquiv.symm_apply_apply]
  exact hb

/-- Divisibility at a single closed point supplies a unit after dividing
by an actual nth power in the function field. -/
theorem exists_stalk_kummer_unit_of_ord_dvd (M : CurveModel K F) (n : ℕ+)
    (u : Fˣ) (x : M.C)
    (hdiv : ∀ xc : closedPoints M.C, xc.val = x →
      (n : ℤ) ∣ (M.placeOfPoint xc).ord (u : F)) :
    ∃ h : M.C.functionField, h ≠ 0 ∧
      M.ffEquiv (u : F) / h ^ (n : ℕ) ∈
        (algebraMap (M.C.presheaf.stalk x) M.C.functionField).range ∧
      h ^ (n : ℕ) / M.ffEquiv (u : F) ∈
        (algebraMap (M.C.presheaf.stalk x) M.C.functionField).range := by
  by_cases hx : x = genericPoint M.C
  · have hsurj : Function.Surjective
        (algebraMap (M.C.presheaf.stalk x) M.C.functionField) := by
      change Function.Surjective
        (M.C.presheaf.stalkSpecializes ((genericPoint_spec M.C).specializes trivial)).hom
      have : IsIso
          (M.C.presheaf.stalkSpecializes ((genericPoint_spec M.C).specializes
            (Set.mem_univ x))) := by
        subst x
        rw [TopCat.Presheaf.stalkSpecializes_refl]
        infer_instance
      exact (ConcreteCategory.bijective_of_isIso
        (M.C.presheaf.stalkSpecializes ((genericPoint_spec M.C).specializes
          (Set.mem_univ x)))).2
    refine ⟨1, one_ne_zero, ?_, ?_⟩
    · exact hsurj _
    · exact hsurj _
  · let xc : closedPoints M.C := ⟨x, isClosed_singleton_of_ne_genericPoint M.toBase x hx⟩
    let w : Place K F := M.placeOfPoint xc
    obtain ⟨q, hq⟩ := hdiv xc rfl
    obtain ⟨t, ht⟩ := w.exists_ord_eq_one
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, w.ord_zero] at ht
      exact zero_ne_one ht
    let a : F := t ^ q
    have ha : a ≠ 0 := zpow_ne_zero q ht0
    have hwa : w.ord a = q := by
      rw [w.ord_zpow, ht, mul_one]
    have huf : (u : F) ≠ 0 := Units.ne_zero u
    have hleft : w.ord ((u : F) / a ^ (n : ℕ)) = 0 := by
      rw [div_eq_mul_inv, w.ord_mul huf (inv_ne_zero (pow_ne_zero _ ha)),
        w.ord_inv, ord_pow, hwa, hq, add_neg_cancel]
    have hright : w.ord (a ^ (n : ℕ) / (u : F)) = 0 := by
      rw [div_eq_mul_inv, w.ord_mul (pow_ne_zero _ ha) (inv_ne_zero huf),
        w.ord_inv, ord_pow, hwa, hq, add_neg_cancel]
    refine ⟨M.ffEquiv a, (map_ne_zero M.ffEquiv).mpr ha, ?_, ?_⟩
    · have hm := ffEquiv_mem_stalk_range M xc ((u : F) / a ^ (n : ℕ))
        (w.mem_of_ord_nonneg (div_ne_zero huf (pow_ne_zero _ ha)) hleft.ge)
      simpa only [map_div₀, map_pow] using hm
    · have hm := ffEquiv_mem_stalk_range M xc (a ^ (n : ℕ) / (u : F))
        (w.mem_of_ord_nonneg (div_ne_zero (pow_ne_zero _ ha) huf) hright.ge)
      simpa only [map_div₀, map_pow] using hm

/-- A divisorial Kummer class with orders divisible away from the boundary
has actual local unit equations at every point of an open subscheme that
avoids that boundary. -/
theorem exists_open_stalk_kummer_unit
    (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
    (a : Pic0.openKummerUnits K F S n)
    {U : Scheme} [IsIntegral U] (j : U ⟶ M.C) [IsOpenImmersion j]
    (hj : DenseRange j)
    (hinterior : ∀ (y : U) (x : closedPoints M.C),
      x.val = j y → M.placeOfPoint x ∉ S)
    (y : U) :
    ∃ h : U.functionField, h ≠ 0 ∧
      j.functionFieldMap hj (M.ffEquiv (a.val : F)) / h ^ (n : ℕ) ∈
        (algebraMap (U.presheaf.stalk y) U.functionField).range ∧
      h ^ (n : ℕ) / j.functionFieldMap hj (M.ffEquiv (a.val : F)) ∈
        (algebraMap (U.presheaf.stalk y) U.functionField).range := by
  obtain ⟨h, hh, hleft, hright⟩ :=
    M.exists_stalk_kummer_unit_of_ord_dvd n a.val (j y)
      (fun x hx => a.property (M.placeOfPoint x) (hinterior y x hx))
  refine ⟨j.functionFieldMap hj h, (map_ne_zero (j.functionFieldMap hj)).mpr hh, ?_, ?_⟩
  · have hm := (j.functionFieldMap_mem_stalk_range_iff_of_isOpenImmersion
        hj y (M.ffEquiv (a.val : F) / h ^ (n : ℕ))).mpr hleft
    simpa only [map_div₀, map_pow] using hm
  · have hm := (j.functionFieldMap_mem_stalk_range_iff_of_isOpenImmersion
        hj y (h ^ (n : ℕ) / M.ffEquiv (a.val : F))).mpr hright
    simpa only [map_div₀, map_pow] using hm

end AlgebraicCurve.CurveModel
