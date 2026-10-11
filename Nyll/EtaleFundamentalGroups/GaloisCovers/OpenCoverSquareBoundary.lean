/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverModelIso

/-! # Smooth proper extensions of actual open covers with the exact boundary -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- A connected finite étale cover of the actual open curve extends to a
finite map of smooth proper curve models. The source open is the original
cover, and its boundary is exactly the inverse image of the original
boundary. -/
theorem exists_open_cover_curveModel_square_boundary
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (W : FiniteEtale X) [IsConnected W] :
    let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let cW : W.left ⟶ Spec (.of K) := W.hom ≫ j ≫ M.toBase
    let : Algebra K W.left.functionField := (baseToFunctionField cW).toAlgebra
    ∃ (N : CurveModel K W.left.functionField)
      (d : N.C ⟶ M.C) (k : W.left ⟶ N.C),
      d ≫ M.toBase = N.toBase ∧ IsFinite d ∧ IsOpenImmersion k ∧
      k ≫ d = W.hom ≫ j ∧
      ∀ y : N.C, y ∉ Set.range k ↔ d y ∉ Set.range j := by
  intro hIntegral cW algW
  obtain ⟨N, d, hd, hfinite, e, he⟩ :=
    exists_curveModel_iso_open_cover_normalization M j W
  let i := FiniteEtale.connectedCoverCompactificationInclusion j W
  let k : W.left ⟶ N.C := i ≫ e.hom
  have : IsOpenImmersion i :=
    FiniteEtale.connectedCoverCompactificationInclusion_isOpenImmersion j W
  have hk : IsOpenImmersion k := by dsimp only [k]; infer_instance
  refine ⟨N, d, k, hd, hfinite, hk, ?_, ?_⟩
  · dsimp only [k]
    rw [Category.assoc, he]
    exact FiniteEtale.connectedCoverCompactificationInclusion_comp j W
  · intro y
    obtain ⟨z, rfl⟩ := e.hom.homeomorph.surjective y
    have hr : e.hom z ∈ Set.range k ↔ z ∈ Set.range i := by
      constructor
      · rintro ⟨w, hw⟩
        refine ⟨w, e.hom.homeomorph.injective ?_⟩
        exact hw
      · rintro ⟨w, rfl⟩
        exact ⟨w, rfl⟩
    have hdpoint : d (e.hom z) =
        (FiniteEtale.connectedCoverGenericComposite W ≫ j).fromNormalization z :=
      congrArg (fun f => f z) he
    change e.hom z ∉ Set.range k ↔ d (e.hom z) ∉ Set.range j
    rw [hr, hdpoint]
    exact FiniteEtale.not_mem_range_connectedCoverCompactificationInclusion j W z

/-- A finite extension of a surjective map over a dense open is surjective. -/
theorem surjective_finite_extension_of_open_square
    {X Y M N : Scheme} [IsIntegral M] [Nonempty X]
    (j : X ⟶ M) [IsOpenImmersion j]
    (f : Y ⟶ X) (hf : Function.Surjective f)
    (k : Y ⟶ N) (d : N ⟶ M) [IsFinite d]
    (hsquare : k ≫ d = f ≫ j) : Function.Surjective d := by
  have hj : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  have hsub : Set.range j ⊆ Set.range d := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hf x
    refine ⟨k y, ?_⟩
    have h := congrArg (fun q => q y) hsquare
    change d (k y) = j (f y) at h
    rw [hy] at h
    exact h
  intro y
  have hy : y ∈ closure (Set.range d) := (hj.mono hsub) y
  rw [d.isClosedMap.isClosed_range.closure_eq] at hy
  exact hy

end EtaleFundamentalGroups
