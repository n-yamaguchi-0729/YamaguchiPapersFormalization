/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.IsClosed_singleton_of_ne_genericPoint
import Nyll.AlgebraicCurves.Geometry.Schemes.isFinite_and_etale_fromNormalization_kummer_of_isIntegrallyClosed
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_pow_eq_of_section_fromNormalization_kummer
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Places.Place_exists_ord_eq_one
import Nyll.AlgebraicCurves.Places.Place_mem_of_ord_nonneg
import Nyll.JacobianVarieties.Kummer.DivisorClasses
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.Topology.Compactness.Compact
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.LocalGeometry.SmoothStalkNormality

/-!
# Finite etale Kummer covers of actual curve models

Divisibility of every valuation order supplies local expressions as a unit times
an `n`th power. Compactness supplies the finite cover required by the concrete
normalization theorem. The result is the actual normalization in the Kummer
root algebra, with no irreducibility or connectedness assumption on that algebra.
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

private theorem exists_stalk_kummer_unit (M : CurveModel K F) (n : ℕ+)
    (u : Pic0.kummerUnits K F n) (x : M.C) :
    ∃ h : M.C.functionField, h ≠ 0 ∧
      M.ffEquiv (u.val : F) / h ^ (n : ℕ) ∈
        (algebraMap (M.C.presheaf.stalk x) M.C.functionField).range ∧
      h ^ (n : ℕ) / M.ffEquiv (u.val : F) ∈
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
    obtain ⟨q, hq⟩ := u.property w
    obtain ⟨t, ht⟩ := w.exists_ord_eq_one
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, w.ord_zero] at ht
      exact zero_ne_one ht
    let a : F := t ^ q
    have ha : a ≠ 0 := zpow_ne_zero q ht0
    have hwa : w.ord a = q := by
      rw [w.ord_zpow, ht, mul_one]
    have huf : (u.val : F) ≠ 0 := Units.ne_zero u.val
    have hleft : w.ord ((u.val : F) / a ^ (n : ℕ)) = 0 := by
      rw [div_eq_mul_inv, w.ord_mul huf (inv_ne_zero (pow_ne_zero _ ha)),
        w.ord_inv, ord_pow, hwa, hq, add_neg_cancel]
    have hright : w.ord (a ^ (n : ℕ) / (u.val : F)) = 0 := by
      rw [div_eq_mul_inv, w.ord_mul (pow_ne_zero _ ha) (inv_ne_zero huf),
        w.ord_inv, ord_pow, hwa, hq, add_neg_cancel]
    refine ⟨M.ffEquiv a, (map_ne_zero M.ffEquiv).mpr ha, ?_, ?_⟩
    · have hm := ffEquiv_mem_stalk_range M xc ((u.val : F) / a ^ (n : ℕ))
        (w.mem_of_ord_nonneg (div_ne_zero huf (pow_ne_zero _ ha)) hleft.ge)
      simpa only [map_div₀, map_pow] using hm
    · have hm := ffEquiv_mem_stalk_range M xc (a ^ (n : ℕ) / (u.val : F))
        (w.mem_of_ord_nonneg (div_ne_zero (pow_ne_zero _ ha) huf) hright.ge)
      simpa only [map_div₀, map_pow] using hm

private theorem exists_open_stalk_ranges {X : Scheme.{u}} [IsIntegral X]
    (x : X) (a b : X.functionField)
    (ha : a ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range)
    (hb : b ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U,
      a ∈ (algebraMap (X.presheaf.stalk y) X.functionField).range ∧
      b ∈ (algebraMap (X.presheaf.stalk y) X.functionField).range := by
  obtain ⟨a₀, ha₀⟩ := ha
  obtain ⟨b₀, hb₀⟩ := hb
  obtain ⟨U, hxU, aU, haU⟩ := X.presheaf.exists_germ_eq a₀
  obtain ⟨V, hxV, bV, hbV⟩ := X.presheaf.exists_germ_eq b₀
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have ha' : X.germToFunctionField U aU = a := by
    rw [← X.algebraMap_germ_eq_germToFunctionField hxU aU, haU, ha₀]
  have hb' : X.germToFunctionField V bV = b := by
    rw [← X.algebraMap_germ_eq_germToFunctionField hxV bV, hbV, hb₀]
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, fun y hy => ⟨?_, ?_⟩⟩
  · refine ⟨X.presheaf.germ U y hy.1 aU, ?_⟩
    rw [X.algebraMap_germ_eq_germToFunctionField, ha']
  · refine ⟨X.presheaf.germ V y hy.2 bV, ?_⟩
    rw [X.algebraMap_germ_eq_germToFunctionField, hb']

/-- Divisible valuation orders give a finite open cover with actual unit local equations. -/
theorem exists_kummer_unit_cover (M : CurveModel K F) (n : ℕ+)
    (u : Pic0.kummerUnits K F n) :
    ∃ (r : ℕ) (U : Fin r → M.C.Opens) (h : Fin r → M.C.functionField),
      (⨆ i, U i) = ⊤ ∧ (∀ i, h i ≠ 0) ∧ ∀ i (x : M.C), x ∈ U i →
        M.ffEquiv (u.val : F) / h i ^ (n : ℕ) ∈
          (algebraMap (M.C.presheaf.stalk x) M.C.functionField).range ∧
        h i ^ (n : ℕ) / M.ffEquiv (u.val : F) ∈
          (algebraMap (M.C.presheaf.stalk x) M.C.functionField).range := by
  classical
  have hloc : ∀ x : M.C, ∃ (h : M.C.functionField) (U : M.C.Opens),
      h ≠ 0 ∧ x ∈ U ∧ ∀ y ∈ U,
        M.ffEquiv (u.val : F) / h ^ (n : ℕ) ∈
          (algebraMap (M.C.presheaf.stalk y) M.C.functionField).range ∧
        h ^ (n : ℕ) / M.ffEquiv (u.val : F) ∈
          (algebraMap (M.C.presheaf.stalk y) M.C.functionField).range := by
    intro x
    obtain ⟨h, hh, hleft, hright⟩ := exists_stalk_kummer_unit M n u x
    obtain ⟨U, hxU, hU⟩ := exists_open_stalk_ranges x _ _ hleft hright
    exact ⟨h, U, hh, hxU, hU⟩
  choose h U hh hxU hU using hloc
  have : CompactSpace M.C := QuasiCompact.compactSpace_of_compactSpace M.toBase
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set M.C))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i => U (e.symm i).val, fun i => h (e.symm i).val,
    ?_, fun i => hh (e.symm i).val, fun i x hx => hU (e.symm i).val x hx⟩
  apply top_le_iff.mp
  intro x _
  obtain ⟨y, hys⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
  obtain ⟨hy, hx⟩ := Set.mem_iUnion.mp hys
  apply Opens.mem_iSup.mpr
  refine ⟨e ⟨y, hy⟩, ?_⟩
  change x ∈ U (e.symm (e ⟨y, hy⟩)).val
  rw [e.symm_apply_apply]
  exact hx

/-- The generic Kummer algebra map whose normalization is the cover. -/
def kummerGenericMap (M : CurveModel K F) (n : ℕ+) (u : Pic0.kummerUnits K F n) :
    Spec (.of (AdjoinRoot (Polynomial.X ^ (n : ℕ) -
      Polynomial.C (M.ffEquiv (u.val : F)) : Polynomial M.C.functionField))) ⟶ M.C :=
  Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField _)) ≫
    M.C.fromSpecStalk (genericPoint M.C)

/-- Normalization in the actual Kummer algebra is finite etale when `n` is a unit. -/
theorem isFiniteEtale_kummer (M : CurveModel K F) (n : ℕ+)
    (hn : IsUnit ((n : ℕ) : K)) (u : Pic0.kummerUnits K F n) :
    IsFiniteEtale (M.kummerGenericMap n u).fromNormalization := by
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  obtain ⟨r, U, h, hU, hh, hdiv⟩ := M.exists_kummer_unit_cover n u
  obtain ⟨hf, he⟩ := isFinite_and_etale_fromNormalization_kummer_of_isIntegrallyClosed
    M.toBase (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase x).2)
    (n : ℕ) hn (M.ffEquiv (u.val : F))
    ((map_ne_zero M.ffEquiv).mpr (Units.ne_zero u.val)) r U hU h hh hdiv
  have : IsFinite (M.kummerGenericMap n u).fromNormalization := hf
  have : Etale (M.kummerGenericMap n u).fromNormalization := he
  exact IsFiniteEtale.mk

/-- The actual finite etale Kummer cover, which may be disconnected. -/
def kummerCover (M : CurveModel K F) (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    (u : Pic0.kummerUnits K F n) : FiniteEtale M.C := by
  have : IsFiniteEtale (M.kummerGenericMap n u).fromNormalization :=
    M.isFiniteEtale_kummer n hn u
  exact FiniteEtale.mk (M.kummerGenericMap n u).fromNormalization

/-- A section of the actual Kummer cover forces its divisor class to vanish. -/
theorem kummerClass_eq_one_of_section [HasPrincipalDivisors K F]
    (M : CurveModel K F) (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    (u : Pic0.kummerUnits K F n) (s : M.C ⟶ (M.kummerCover n hn u).left)
    (hs : s ≫ (M.kummerCover n hn u).hom = 𝟙 M.C) : Pic0.kummerClass n u = 1 := by
  obtain ⟨a, ha⟩ := exists_pow_eq_of_section_fromNormalization_kummer (n : ℕ)
    (M.ffEquiv (u.val : F)) ((map_ne_zero M.ffEquiv).mpr (Units.ne_zero u.val)) s hs
  let b : F := M.ffEquiv.symm a
  have hbpow : b ^ (n : ℕ) = (u.val : F) := by
    have he := congrArg M.ffEquiv.symm ha
    simpa only [map_pow, RingEquiv.symm_apply_apply] using he
  have hb : b ≠ 0 := by
    intro h0
    rw [h0, zero_pow n.ne_zero] at hbpow
    exact Units.ne_zero u.val hbpow.symm
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) b hb
  let D₀ : Divisor.degZero (K := K) (F := F) := ⟨D, hdeg⟩
  have hclass := Pic0.kummerClass_eq n u D₀ (fun v => by
    change v.ord (u.val : F) = (n : ℤ) * D v
    rw [← hbpow, ord_pow, hD v])
  have hz : Pic0.mk D₀ = 0 := (Pic0.mk_eq_zero_iff D₀).mpr ⟨b, hb, hD⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact hclass.trans hz

end AlgebraicCurve.CurveModel
