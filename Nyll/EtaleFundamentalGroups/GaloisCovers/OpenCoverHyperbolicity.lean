/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverSquareBoundary
import Nyll.AlgebraicCurves.Models.OpenCoverRiemannHurwitz

/-!
# Actual connected finite étale covers preserve open hyperbolicity

The proper source model, the original source open, its boundary and the
Euler-characteristic formula are constructed from the actual cover.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

theorem exists_hyperbolic_open_cover_model
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (W : FiniteEtale X) [IsConnected W]
    (hhyperbolic : 0 <
      2 * (genusFF K F : ℤ) + (M.openBoundaryPlaces_finite j).toFinset.card - 2) :
    let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let cW : W.left ⟶ Spec (.of K) := W.hom ≫ j ≫ M.toBase
    let : Algebra K W.left.functionField := (baseToFunctionField cW).toAlgebra
    ∃ (N : CurveModel K W.left.functionField)
      (d : N.C ⟶ M.C) (k : W.left ⟶ N.C)
      (_ : IsOpenImmersion k),
      d ≫ M.toBase = N.toBase ∧ IsFinite d ∧
      k ≫ d = W.hom ≫ j ∧
      (∀ y : N.C, y ∉ Set.range k ↔ d y ∉ Set.range j) ∧
      0 < 2 * (genusFF K W.left.functionField : ℤ) +
        (N.openBoundaryPlaces_finite k).toFinset.card - 2 := by
  intro hIntegral cW algW
  have : IsIntegral ((Functor.id Scheme).obj W.left) := hIntegral
  have : IsIntegral ((Functor.fromPUnit X).obj W.right) :=
    inferInstanceAs (IsIntegral X)
  obtain ⟨N, d, k, hd, hfinite, hk, hsquare, hboundary⟩ :=
    exists_open_cover_curveModel_square_boundary M j W
  have : IsOpenImmersion k := hk
  have : IsFinite d := hfinite
  have : IsFiniteEtale W.hom := W.prop
  have : Surjective W.hom := IsFiniteEtale.surjective W.hom
  have hsurj : Function.Surjective d :=
    surjective_finite_extension_of_open_square j W.hom W.hom.surjective k d hsquare
  have : Etale (k ≫ d) := by
    rw [hsquare]
    infer_instance
  have hrh := M.two_mul_genus_add_openBoundary_sub_two_eq N d hd hsurj j k hboundary
  let φ := M.finiteCurveFieldMap N d hd hsurj
  let : Algebra F W.left.functionField := algebraAlong φ
  have : FiniteDimensional F W.left.functionField :=
    M.finiteCurveFieldMap_finite N d hd hsurj
  have hdegree : (0 : ℤ) < finrankAlong K φ := by
    exact_mod_cast (Module.finrank_pos (R := F) (M := W.left.functionField))
  refine ⟨N, d, k, hk, hd, hfinite, hsquare, hboundary, ?_⟩
  rw [hrh]
  exact mul_pos hdegree hhyperbolic

end EtaleFundamentalGroups
