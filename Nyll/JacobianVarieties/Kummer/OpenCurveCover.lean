/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.OpenLocalUnits
import Nyll.AlgebraicCurves.Geometry.Schemes.isFinite_and_etale_fromNormalization_kummer_of_isIntegrallyClosed
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.LocalGeometry.SmoothStalkNormality
import Mathlib.Topology.Compactness.Compact

/-!
# Actual Kummer covers of open curves

The normalization construction is applied to the actual open curve, using
local unit equations proved from its interior valuation orders. The cover
is not required to extend étale across the removed boundary.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicCurve.CurveModel

universe u v

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]

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

/-- Pointwise unit equations admit a finite open cover on a compact
integral scheme. -/
theorem exists_finite_kummer_unit_cover
    {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
    (n : ℕ+) (a : X.functionField)
    (hlocal : ∀ x : X, ∃ h : X.functionField, h ≠ 0 ∧
      a / h ^ (n : ℕ) ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range ∧
      h ^ (n : ℕ) / a ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ (r : ℕ) (V : Fin r → X.Opens) (h : Fin r → X.functionField),
      (⨆ i, V i) = ⊤ ∧ (∀ i, h i ≠ 0) ∧ ∀ i (x : X), x ∈ V i →
        a / h i ^ (n : ℕ) ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range ∧
        h i ^ (n : ℕ) / a ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  classical
  have hloc : ∀ x : X, ∃ (h : X.functionField) (V : X.Opens),
      h ≠ 0 ∧ x ∈ V ∧ ∀ y ∈ V,
        a / h ^ (n : ℕ) ∈ (algebraMap (X.presheaf.stalk y) X.functionField).range ∧
        h ^ (n : ℕ) / a ∈ (algebraMap (X.presheaf.stalk y) X.functionField).range := by
    intro x
    obtain ⟨h, hh, hleft, hright⟩ := hlocal x
    obtain ⟨V, hxV, hV⟩ := exists_open_stalk_ranges x _ _ hleft hright
    exact ⟨h, V, hh, hxV, hV⟩
  choose h V hh hxV hV using hloc
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i => V (e.symm i).val, fun i => h (e.symm i).val,
    ?_, fun i => hh (e.symm i).val, fun i x hx => hV (e.symm i).val x hx⟩
  apply top_le_iff.mp
  intro x _
  obtain ⟨y, hys⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
  obtain ⟨hy, hx⟩ := Set.mem_iUnion.mp hys
  apply Opens.mem_iSup.mpr
  refine ⟨e ⟨y, hy⟩, ?_⟩
  change x ∈ V (e.symm (e ⟨y, hy⟩)).val
  rw [e.symm_apply_apply]
  exact hx

/-- The actual generic Kummer equation over an open subscheme of a
proper curve model. -/
def openKummerGenericMap
    (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
    (a : Pic0.openKummerUnits K F S n)
    {U : Scheme.{u}} [IsIntegral U] (j : U ⟶ M.C) (hj : DenseRange j) :
    Spec (.of (AdjoinRoot (Polynomial.X ^ (n : ℕ) -
      Polynomial.C (j.functionFieldMap hj (M.ffEquiv (a.val : F))) :
        Polynomial U.functionField))) ⟶ U :=
  Spec.map (CommRingCat.ofHom (algebraMap U.functionField _)) ≫
    U.fromSpecStalk (genericPoint U)

/-- Normalizing the actual open curve in its Kummer root algebra gives a
finite étale cover when the valuation orders are divisible at all interior
points. Compactness here is quasi-compactness of the open curve. -/
theorem isFiniteEtale_openKummer
    (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
    (hn : IsUnit ((n : ℕ) : K)) (a : Pic0.openKummerUnits K F S n)
    {U : Scheme.{u}} [IsIntegral U] [CompactSpace U]
    (j : U ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hinterior : ∀ (y : U) (x : closedPoints M.C),
      x.val = j y → M.placeOfPoint x ∉ S) :
    IsFiniteEtale (M.openKummerGenericMap S n a j hj).fromNormalization := by
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : Smooth (j ≫ M.toBase) := inferInstance
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  obtain ⟨r, V, h, hV, hh, hdiv⟩ := exists_finite_kummer_unit_cover n
    (j.functionFieldMap hj (M.ffEquiv (a.val : F)))
    (M.exists_open_stalk_kummer_unit S n a j hj hinterior)
  have ha : j.functionFieldMap hj (M.ffEquiv (a.val : F)) ≠ 0 :=
    (map_ne_zero (j.functionFieldMap hj)).mpr
      ((map_ne_zero M.ffEquiv).mpr (Units.ne_zero a.val))
  obtain ⟨hf, he⟩ := isFinite_and_etale_fromNormalization_kummer_of_isIntegrallyClosed
    (j ≫ M.toBase)
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk (j ≫ M.toBase) x).2)
    (n : ℕ) hn (j.functionFieldMap hj (M.ffEquiv (a.val : F))) ha
    r V hV h hh hdiv
  have : IsFinite (M.openKummerGenericMap S n a j hj).fromNormalization := hf
  have : Etale (M.openKummerGenericMap S n a j hj).fromNormalization := he
  exact IsFiniteEtale.mk

/-- The actual finite étale Kummer cover of the open curve. -/
def openKummerCover
    (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
    (hn : IsUnit ((n : ℕ) : K)) (a : Pic0.openKummerUnits K F S n)
    {U : Scheme.{u}} [IsIntegral U] [CompactSpace U]
    (j : U ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hinterior : ∀ (y : U) (x : closedPoints M.C),
      x.val = j y → M.placeOfPoint x ∉ S) : FiniteEtale U := by
  have : IsFiniteEtale (M.openKummerGenericMap S n a j hj).fromNormalization :=
    M.isFiniteEtale_openKummer S n hn a j hj hinterior
  exact FiniteEtale.mk (M.openKummerGenericMap S n a j hj).fromNormalization

end AlgebraicCurve.CurveModel
