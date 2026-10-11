/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.IsCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Nyll.AlgebraicCurves.Models.FiniteCurveBoundaryMap
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.OpenBoundary
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_iff_exists_transcendental_finiteDimensional

/-! # Riemann--Hurwitz for an actual open-cover square -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicCurves.Models.Proofs
open CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite.AlgebraicCurve

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The actual omitted-place counts satisfy the open Euler-characteristic
formula. Unramifiedness is proved from the open restriction, and the
boundary preimage is translated through the actual map on local rings. -/
theorem two_mul_genus_add_openBoundary_sub_two_eq
    {K F E : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Field E] [Algebra K F] [Algebra K E]
    (M : CurveModel K F) (N : CurveModel K E)
    (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase)
    [IsFinite d] (hsurj : Function.Surjective d)
    {X Y : Scheme} [Nonempty X] [Nonempty Y]
    (j : X ⟶ M.C) [IsOpenImmersion j]
    (k : Y ⟶ N.C) [IsOpenImmersion k] [FormallyUnramified (k ≫ d)]
    (hboundary : ∀ y : N.C, y ∉ Set.range k ↔ d y ∉ Set.range j) :
    2 * (genusFF K E : ℤ) + (N.openBoundaryPlaces_finite k).toFinset.card - 2 =
      (finrankAlong K (M.finiteCurveFieldMap N d hd hsurj) : ℤ) *
        (2 * (genusFF K F : ℤ) + (M.openBoundaryPlaces_finite j).toFinset.card - 2) := by
  classical
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  have : IsCurveOver K E :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one N.toBase
      N.ffEquiv N.ffEquiv_algebraMap
  have : Algebra.EssFiniteType K F := by
    let : Algebra K M.C.functionField := (baseToFunctionField M.toBase).toAlgebra
    let e : F ≃ₐ[K] M.C.functionField :=
      AlgEquiv.ofRingEquiv (f := M.ffEquiv) M.ffEquiv_algebraMap
    exact (Algebra.EssFiniteType.iff_of_algEquiv e).mpr
      (IsCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one.SmoothModelFunctionField.stageA
        M.toBase).1
  have : Algebra.EssFiniteType K E := by
    let : Algebra K N.C.functionField := (baseToFunctionField N.toBase).toAlgebra
    let e : E ≃ₐ[K] N.C.functionField :=
      AlgEquiv.ofRingEquiv (f := N.ffEquiv) N.ffEquiv_algebraMap
    exact (Algebra.EssFiniteType.iff_of_algEquiv e).mpr
      (IsCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one.SmoothModelFunctionField.stageA
        N.toBase).1
  let φ := M.finiteCurveFieldMap N d hd hsurj
  let hφ := M.finiteCurveFieldMap_integral N d hd hsurj
  have hfin : FiniteAlong K φ := M.finiteCurveFieldMap_finite N d hd hsurj
  let : Algebra F E := algebraAlong φ
  have : FiniteDimensional F E := hfin
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have hsep : SeparableAlong K φ := by
    change Algebra.IsSeparable F E
    infer_instance
  let S := (M.openBoundaryPlaces_finite j).toFinset
  let T := (N.openBoundaryPlaces_finite k).toFinset
  have hboundaryPlaces := M.openBoundaryPlaces_eq_restrict_preimage N d hd hsurj j k hboundary
  have hT : T = boundaryAbove φ hφ S := by
    ext w
    change w ∈ (N.openBoundaryPlaces_finite k).toFinset ↔ _
    rw [Set.Finite.mem_toFinset, mem_boundaryAbove_iff]
    change w ∈ N.openBoundaryPlaces k ↔
      w.restrictAlong φ hφ ∈ (M.openBoundaryPlaces_finite j).toFinset
    rw [Set.Finite.mem_toFinset, hboundaryPlaces]
    rfl
  have hu (w : Place K E) (hw : w.restrictAlong φ hφ ∉ S) :
      Place.ramificationIndexAlong φ w = 1 := by
    apply M.finiteCurveFieldMap_unramified_on_open N d hd hsurj k w
    intro h
    have hr : w.restrictAlong φ hφ ∈ M.openBoundaryPlaces j := by
      rw [hboundaryPlaces] at h
      exact h
    exact hw ((M.openBoundaryPlaces_finite j).mem_toFinset.mpr hr)
  obtain ⟨t, ht, hfinite, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have h := two_mul_genus_add_boundary_sub_two_eq φ hφ hfin hsep
    ⟨t, ht, hfinite⟩ S hu
  rw [← hT] at h
  exact h

end AlgebraicCurve.CurveModel
