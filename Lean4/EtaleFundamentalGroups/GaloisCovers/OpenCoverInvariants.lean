/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.OpenCoverDegree
import EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms
import AlgebraicCurves.Places.Place_restrictAlong_surjective

/-! # Degree and nonempty boundary of actual open covers -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The actual finite extension has a place above every omitted place,
so the source of the open cover still has nonempty boundary. -/
theorem openBoundary_nonempty_of_finite_square
    {K F E : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Field E] [Algebra K F] [Algebra K E]
    (M : CurveModel K F) (N : CurveModel K E)
    (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase)
    [IsFinite d] (hsurj : Function.Surjective d)
    {X Y : Scheme} (j : X ⟶ M.C) (k : Y ⟶ N.C)
    (hboundary : ∀ y : N.C, y ∉ Set.range k ↔ d y ∉ Set.range j)
    (hS : (M.openBoundaryPlaces j).Nonempty) :
    (N.openBoundaryPlaces k).Nonempty := by
  let φ := M.finiteCurveFieldMap N d hd hsurj
  let hφ := M.finiteCurveFieldMap_integral N d hd hsurj
  have hfin := M.finiteCurveFieldMap_finite N d hd hsurj
  let : Algebra F E := algebraAlong φ
  have : FiniteDimensional F E := hfin
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have hsep : SeparableAlong K φ := by change Algebra.IsSeparable F E; infer_instance
  obtain ⟨v, hv⟩ := hS
  obtain ⟨w, hw⟩ := Place.restrictAlong_surjective φ hφ hfin hsep v
  refine ⟨w, ?_⟩
  rw [M.openBoundaryPlaces_eq_restrict_preimage N d hd hsurj j k hboundary]
  change w.restrictAlong φ hφ ∈ M.openBoundaryPlaces j
  change w.restrictAlong φ hφ = v at hw
  rw [hw]
  exact hv

/-- A nonidentity actual Galois deck transformation forces the actual
function-field degree to be greater than one. -/
theorem one_lt_functionField_degree_of_nontrivial_galois_deck
    {X : Scheme} [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (W : FiniteEtale X) [IsGalois W] (σ : Aut W) (hσ : σ ≠ 1) :
    let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let : Algebra X.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    1 < Module.finrank X.functionField W.left.functionField := by
  intro hIntegral algW
  rw [← natCard_finiteEtaleAut_eq_finrank_functionField_of_isGalois W inferInstance]
  by_contra h
  have hc : Nat.card (Aut W) = 1 :=
    Nat.le_antisymm (Nat.le_of_not_gt h) (Nat.succ_le_of_lt Nat.card_pos)
  have hs := (Nat.card_eq_one_iff_unique.mp hc).1
  exact hσ (hs.elim σ 1)

end EtaleFundamentalGroups
