/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.CurveModel_nonempty_of_perfectField
import Nyll.AlgebraicCurves.Models.CurveModel_exists_finite_flat_hom_of_algHom
import Nyll.AlgebraicCurves.Models.IsCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_iff_exists_transcendental_finiteDimensional
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenPlaceTransport
import Nyll.EtaleFundamentalGroups.Normalization.GenericFieldSourceNaturality
import Nyll.EtaleFundamentalGroups.Purity.ConnectedCoverGenericNormalizationFinite

/-!
# The finite proper model of an actual connected open cover

The function field, its scalar map and its finite extension map are taken
from the original finite étale scheme cover. Existing smooth proper model
construction and finite-map extension then produce the proper curve map.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open CategoryTheory.PreGaloisCategory
open AlgebraicCurves.Models.Proofs.IsCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one

namespace EtaleFundamentalGroups

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The function field of a connected finite étale open cover has a smooth
proper model whose finite map extends the original generic morphism. -/
theorem exists_finite_curveModel_map_of_open_cover
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme} [IsIntegral X] [IsNormalIntegral X]
    (j : X ⟶ M.C) [IsOpenImmersion j]
    (W : FiniteEtale X) [IsConnected W] :
    let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let cW : W.left ⟶ Spec (.of K) := W.hom ≫ j ≫ M.toBase
    let : Algebra K W.left.functionField := (baseToFunctionField cW).toAlgebra
    ∃ (N : CurveModel K W.left.functionField) (d : N.C ⟶ M.C),
      d ≫ M.toBase = N.toBase ∧ IsFinite d ∧
      (Spec.map (CommRingCat.ofHom N.ffEquiv.symm.toRingHom) ≫
        N.C.fromSpecStalk (genericPoint N.C)) ≫ d =
          W.left.fromSpecStalk (genericPoint W.left) ≫ W.hom ≫ j := by
  intro hWIntegral cW algW
  have : IsIntegral ((Functor.id Scheme).obj W.left) := hWIntegral
  have : IsIntegral ((Functor.fromPUnit X).obj W.right) :=
    inferInstanceAs (IsIntegral X)
  have : IsFiniteEtale W.hom := W.prop
  have : SmoothOfRelativeDimension 1 (j ≫ M.toBase) :=
    smoothOfRelativeDimension_comp 0 1 j M.toBase
  have : SmoothOfRelativeDimension 1 cW :=
    smoothOfRelativeDimension_comp 0 1 W.hom (j ≫ M.toBase)
  have : IsCurveOver K W.left.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one (C := W.left) cW
      (RingEquiv.refl _) (fun _ => rfl)
  have : Algebra.EssFiniteType K W.left.functionField :=
    (SmoothModelFunctionField.stageA (C := W.left) cW).1
  obtain ⟨t, ht, hfinite, _⟩ :=
    (isCurveOver_iff_exists_transcendental_finiteDimensional
      (K := K) (F := W.left.functionField)).mp inferInstance
  obtain ⟨N⟩ := CurveModel.nonempty_of_perfectField K W.left.functionField
    ⟨t, ht, hfinite⟩
  let hj : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  let hw : DenseRange W.hom := finiteEtale_hom_denseRange_of_isConnected W
  let E := M.ffEquiv.trans j.functionFieldRingEquivOfIsOpenImmersion
  let : Algebra K X.functionField := (baseToFunctionField (j ≫ M.toBase)).toAlgebra
  let e : F ≃ₐ[K] X.functionField :=
    AlgEquiv.ofRingEquiv (f := E) (M.openFunctionFieldEquiv_algebraMap j)
  let φ : F →ₐ[K] W.left.functionField :=
    (Scheme.Hom.functionFieldAlgHomOver (X := X) (Y := W.left)
      (j ≫ M.toBase) W.hom hw).comp e.toAlgHom
  let : Algebra X.functionField W.left.functionField :=
    finiteEtaleFunctionFieldAlgebra W
  have : FiniteDimensional X.functionField W.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : Algebra F W.left.functionField := algebraAlong φ
  have hcompat :
      (algebraMap F W.left.functionField).comp E.symm.toRingHom =
        (RingEquiv.refl W.left.functionField).toRingHom.comp
          (algebraMap X.functionField W.left.functionField) := by
    ext a
    change W.hom.functionFieldMap hw (E (E.symm a)) = W.hom.functionFieldMap hw a
    rw [E.apply_symm_apply]
  have hfin : FiniteAlong K φ :=
    Module.Finite.of_equiv_equiv E.symm (RingEquiv.refl W.left.functionField) hcompat
  have : FiniteDimensional F W.left.functionField := hfin
  have hφ : φ.toRingHom.IsIntegral := fun a =>
    Algebra.IsIntegral.isIntegral (R := F) a
  obtain ⟨d, hd, hdfinite, _, _, _, hgeneric, _, _⟩ :=
    M.exists_finite_flat_hom_of_algHom N φ hφ hfin
  refine ⟨N, d, hd, hdfinite, ?_⟩
  have hmap : φ.toRingHom.comp M.ffEquiv.symm.toRingHom =
      (W.hom.functionFieldMap hw).comp (j.functionFieldMap hj) := by
    ext a
    change W.hom.functionFieldMap hw
      (j.functionFieldMap hj (M.ffEquiv (M.ffEquiv.symm a))) = _
    rw [M.ffEquiv.apply_symm_apply]
    rfl
  rw [Category.assoc, hgeneric, ← Category.assoc, ← Spec.map_comp]
  have hcancel :
      CommRingCat.ofHom (N.ffEquiv.toRingHom.comp
        (φ.toRingHom.comp M.ffEquiv.symm.toRingHom)) ≫
        CommRingCat.ofHom N.ffEquiv.symm.toRingHom =
      CommRingCat.ofHom ((W.hom.functionFieldMap hw).comp (j.functionFieldMap hj)) := by
    apply CommRingCat.hom_ext
    ext a
    change N.ffEquiv.symm (N.ffEquiv (φ (M.ffEquiv.symm a))) = _
    rw [N.ffEquiv.symm_apply_apply]
    exact DFunLike.congr_fun hmap a
  rw [hcancel]
  change Spec.map (CommRingCat.ofHom (j.functionFieldMap hj) ≫
    CommRingCat.ofHom (W.hom.functionFieldMap hw)) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, Spec_functionFieldMap_fromSpecStalk j hj,
    ← Category.assoc, Spec_functionFieldMap_fromSpecStalk (X := X) (Y := W.left) W.hom hw,
    Category.assoc]

end EtaleFundamentalGroups
