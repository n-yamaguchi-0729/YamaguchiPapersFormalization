/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.OpenCurveCover
import Nyll.JacobianVarieties.Kummer.CurveCoverLocalCoordinates
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_root_fromNormalization_kummer_existsUnique_lift
import Nyll.SchemeTheory.LocalGeometry.SmoothStalkNormality
import Mathlib.AlgebraicGeometry.Normalization

/-!
# Actual affine root coordinates on the normalized Kummer cover

Every point of the original curve has an affine neighborhood on which the
actual normalized cover represents roots of a unit. Its distinguished section
is compared with the literal root of the original generic Kummer algebra.
This retained comparison is necessary to identify the previously constructed
root-scaling automorphisms on geometric fibers.

The local sections are supplied by the existing Kummer normalization theorem,
whose Anthropic FLT attribution is retained in its original source file.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace AlgebraicCurve.CurveModel.OpenKummer

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
  (w : Pic0.openKummerUnits K F S n)
  {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hinterior : ∀ (y : X) (x : closedPoints M.C),
    x.val = j y → M.placeOfPoint x ∉ S)

include hinterior in
/-- Around each actual point, the normalized Kummer cover represents roots of
an actual unit, and its distinguished section is the original generic root
divided by the explicitly supplied local rational factor. -/
theorem exists_kummer_root_chart (hn : IsUnit ((n : ℕ) : K)) (x : X) :
    let f := M.openKummerGenericMap S n w j hj
    let N := f.normalization
    let π := f.fromNormalization
    let A := AdjoinRoot (Polynomial.X ^ (n : ℕ) -
      Polynomial.C (j.functionFieldMap hj (M.ffEquiv (w.val : F))) : Polynomial X.functionField)
    ∃ (V : X.Opens) (_hV : IsAffineOpen V), x ∈ V ∧
      ∃ (h : X.functionField) (_hh : h ≠ 0) (v : Γ(X, V)), IsUnit v ∧
        ∃ T : Γ(N, π ⁻¹ᵁ V),
          T ^ (n : ℕ) = π.app V v ∧
          f.toNormalization.app (π ⁻¹ᵁ V) T =
            (Spec (.of A)).presheaf.map (homOfLE le_top).op
              ((Scheme.ΓSpecIso (.of A)).inv
                (algebraMap X.functionField A h⁻¹ * AdjoinRoot.root _)) ∧
          ∀ (Z : Scheme.{u}) (z : Z ⟶ X), z ⁻¹ᵁ V = ⊤ →
            ∀ τ : Γ(Z, ⊤), Z.presheaf.map (homOfLE le_top).op τ ^ (n : ℕ) = z.app V v →
              ∃! s : Z ⟶ N, s ≫ π = z ∧
                s.app (π ⁻¹ᵁ V) T = Z.presheaf.map (homOfLE le_top).op τ := by
  intro f N π A
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : Smooth (j ≫ M.toBase) := inferInstance
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have hnorm : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y) :=
    fun y => (Smooth.isDomain_and_isIntegrallyClosed_stalk (j ≫ M.toBase) y).2
  obtain ⟨r, U, h, hU, hh, hdiv⟩ := exists_finite_kummer_unit_cover n
    (j.functionFieldMap hj (M.ffEquiv (w.val : F)))
    (M.exists_open_stalk_kummer_unit S n w j hj hinterior)
  have hx : x ∈ (⨆ i, U i) := hU.symm ▸ Set.mem_univ x
  have haex : ∃ a, x ∈ U a := Opens.mem_iSup.mp hx
  let a : Fin r := Classical.choose haex
  have hxa : x ∈ U a := Classical.choose_spec haex
  have hVex : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U a := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxa (U a).isOpen
    exact ⟨V, hV, hxV, hVU⟩
  let V : X.Opens := Classical.choose hVex
  have hV : IsAffineOpen V := (Classical.choose_spec hVex).1
  have hxV : x ∈ V := (Classical.choose_spec hVex).2.1
  have hVU : V ≤ U a := (Classical.choose_spec hVex).2.2
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  refine ⟨V, hV, hxV, h a, hh a, ?_⟩
  exact exists_affine_root_coordinate (R := K) (X := X) (j ≫ M.toBase) hnorm n hn
    (j.functionFieldMap hj (M.ffEquiv (w.val : F)))
    (h a) ((map_ne_zero (j.functionFieldMap hj)).mpr
      ((map_ne_zero M.ffEquiv).mpr (Units.ne_zero w.val))) (hh a) V hV
    (fun y hy => hdiv a y (hVU hy))

end AlgebraicCurve.CurveModel.OpenKummer
