/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Models.FiniteCurveBoundaryMap
import EtaleFundamentalGroups.Normalization.GenericFieldSourceNaturality
import EtaleFundamentalGroups.FiniteEtale.FunctionField
import EtaleFundamentalGroups.GaloisCovers.OpenFunctionField

/-! # The degree of the compactified map is the actual open-cover degree -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

theorem finiteCurveFieldMap_eq_actual_functionFieldMap
    {K F E : Type} [Field K] [IsAlgClosed K]
    [Field F] [Field E] [Algebra K F] [Algebra K E]
    (M : CurveModel K F) (N : CurveModel K E)
    (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase)
    [IsFinite d] (hsurj : Function.Surjective d) (a : F) :
    N.ffEquiv (M.finiteCurveFieldMap N d hd hsurj a) =
      d.functionFieldMap hsurj.denseRange (M.ffEquiv a) := by
  let φ := M.finiteCurveFieldMap N d hd hsurj
  have hgen := M.finiteCurveFieldMap_generic N d hd hsurj
  have hnatural := Spec_functionFieldMap_fromSpecStalk d hsurj.denseRange
  have hcat : CommRingCat.ofHom (d.functionFieldMap hsurj.denseRange) =
      CommRingCat.ofHom (N.ffEquiv.toRingHom.comp
        (φ.toRingHom.comp M.ffEquiv.symm.toRingHom)) := by
    apply Spec.map_injective
    apply (cancel_mono (M.C.fromSpecStalk (genericPoint M.C))).mp
    exact hnatural.trans hgen
  have h := congrArg (fun f => f.hom (M.ffEquiv a)) hcat
  change d.functionFieldMap hsurj.denseRange (M.ffEquiv a) =
    N.ffEquiv (φ (M.ffEquiv.symm (M.ffEquiv a))) at h
  rw [M.ffEquiv.symm_apply_apply] at h
  exact h.symm

/-- Degree comparison for the original open cover and its actual proper
extension square. No numerical degree comparison is assumed. -/
theorem finrankAlong_openCover_eq_actual
    {K F E : Type} [Field K] [IsAlgClosed K]
    [Field F] [Field E] [Algebra K F] [Algebra K E]
    (M : CurveModel K F) (N : CurveModel K E)
    {X : Scheme} [IsIntegral X] [IsNormalIntegral X]
    (j : X ⟶ M.C) [IsOpenImmersion j]
    (W : FiniteEtale X) [IsConnected W]
    (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase)
    [IsFinite d] (hsurj : Function.Surjective d)
    (k : W.left ⟶ N.C) [IsOpenImmersion k]
    (hsquare : k ≫ d = W.hom ≫ j) :
    let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let : Algebra X.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    finrankAlong K (M.finiteCurveFieldMap N d hd hsurj) =
      Module.finrank X.functionField W.left.functionField := by
  intro hIntegral algW
  have : IsIntegral ((Functor.id Scheme).obj W.left) := hIntegral
  have : IsIntegral ((Functor.fromPUnit X).obj W.right) :=
    inferInstanceAs (IsIntegral X)
  let hj : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  let hk : DenseRange k :=
    k.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace k
  let hw : DenseRange W.hom := finiteEtale_hom_denseRange_of_isConnected W
  let φ := M.finiteCurveFieldMap N d hd hsurj
  let : Algebra F E := algebraAlong φ
  have hcomp :
      (k.functionFieldMap hk).comp (d.functionFieldMap hsurj.denseRange) =
        (W.hom.functionFieldMap hw).comp (j.functionFieldMap hj) := by
    rw [functionFieldMap_comp_of_dense d hsurj.denseRange k hk,
      functionFieldMap_comp_of_dense (X := M.C) (Y := X) (Z := W.left) j hj W.hom hw]
    congr 1
  refine Algebra.finrank_eq_of_equiv_equiv
    (M.ffEquiv.trans j.functionFieldRingEquivOfIsOpenImmersion)
    (N.ffEquiv.trans k.functionFieldRingEquivOfIsOpenImmersion) ?_
  ext a
  change W.hom.functionFieldMap hw (j.functionFieldMap hj (M.ffEquiv a)) =
    k.functionFieldMap hk (N.ffEquiv (φ a))
  rw [finiteCurveFieldMap_eq_actual_functionFieldMap M N d hd hsurj a]
  exact (DFunLike.congr_fun hcomp (M.ffEquiv a)).symm

end EtaleFundamentalGroups
