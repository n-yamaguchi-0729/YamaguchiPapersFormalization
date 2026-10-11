/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.OpenCoverFiniteModel
import EtaleFundamentalGroups.GaloisCovers.CompactificationBoundary
import EtaleFundamentalGroups.Normalization.FiniteNormalFieldSource
import SchemeTheory.LocalGeometry.SmoothStalkNormality

/-!
# The actual normalization compactification is a smooth proper curve model

The comparison is over the original base curve. It identifies the chosen
smooth proper function-field model with the actual normalization containing
the original open cover.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

private local instance fieldSpecQuasiCompact
    {L : Type} [Field L] {S : Scheme} (f : Spec (.of L) ⟶ S) :
    QuasiCompact f where
  isCompact_preimage U _ _ := (Set.toFinite (f ⁻¹' U)).isCompact

private theorem transport_normalization_model
    {A B N : Scheme} (g q : A ⟶ B)
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact q] [QuasiSeparated q]
    (h : g = q) (d : N ⟶ B)
    (e : g.normalization ≅ N)
    (he : e.hom ≫ d = g.fromNormalization) :
    ∃ e' : q.normalization ≅ N, e'.hom ≫ d = q.fromNormalization := by
  subst q
  exact ⟨e, he⟩

/-- The actual proper normalization has a smooth proper curve-model
identification over the original base, not just a function-field equivalence. -/
theorem exists_curveModel_iso_open_cover_normalization
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (W : FiniteEtale X) [IsConnected W] :
    let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let cW : W.left ⟶ Spec (.of K) := W.hom ≫ j ≫ M.toBase
    let : Algebra K W.left.functionField := (baseToFunctionField cW).toAlgebra
    ∃ (N : CurveModel K W.left.functionField) (d : N.C ⟶ M.C),
      d ≫ M.toBase = N.toBase ∧ IsFinite d ∧
      ∃ e : (FiniteEtale.connectedCoverGenericComposite W ≫ j).normalization ≅ N.C,
        e.hom ≫ d = (FiniteEtale.connectedCoverGenericComposite W ≫ j).fromNormalization := by
  intro hIntegral cW algW
  obtain ⟨N, d, hd, hfinite, hgeneric⟩ :=
    exists_finite_curveModel_map_of_open_cover M j W
  have : IsFinite d := hfinite
  have : Smooth N.toBase := SmoothOfRelativeDimension.smooth 1 N.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral N.C := IsNormalIntegral.of_stalks N.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk N.toBase x).2)
  let eF := Scheme.Spec.mapIso N.ffEquiv.symm.toCommRingCatIso.op
  let η := N.C.fromSpecStalk (genericPoint N.C)
  have : IsDominant η := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro z
    apply (genericPoint_specializes z).mem_closed isClosed_closure
    exact subset_closure ⟨IsLocalRing.closedPoint N.C.functionField,
      Scheme.fromSpecStalk_closedPoint (X := N.C) (x := genericPoint N.C)⟩
  let p : Spec (.of W.left.functionField) ⟶ N.C := eF.hom ≫ η
  have : IsDominant p := by dsimp only [p]; infer_instance
  have : IsPreimmersion p := by dsimp only [p, η]; infer_instance
  have hid : CommRingCat.ofHom
      (algebraMap W.left.functionField W.left.functionField) = 𝟙 _ := rfl
  have hp : p ≫ d = FiniteEtale.connectedCoverGenericComposite W ≫ j := by
    change (Spec.map (CommRingCat.ofHom N.ffEquiv.symm.toRingHom) ≫
      N.C.fromSpecStalk (genericPoint N.C)) ≫ d = _
    simpa only [FiniteEtale.connectedCoverGenericComposite,
      FiniteEtale.connectedCoverGenericMorphism, Scheme.genericExtensionMorphism,
      hid, Spec.map_id, Category.id_comp, Category.assoc] using hgeneric
  obtain ⟨e, he⟩ := transport_normalization_model (p ≫ d)
    (FiniteEtale.connectedCoverGenericComposite W ≫ j) hp d
    (finiteNormalFieldSourceIso d p)
    (finiteNormalFieldSourceIso_hom_fromNormalization d p)
  exact ⟨N, d, hd, hfinite, e, he⟩

end EtaleFundamentalGroups
