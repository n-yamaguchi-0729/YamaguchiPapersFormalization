/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Models.FiniteEtaleRiemannHurwitz
import EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms

/-! # Comparing the actual étale cover degree with curve-model degree -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open AlgebraicCurves.Models.Proofs
open CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite.AlgebraicCurve

namespace AlgebraicCurve.CurveModel

private theorem eqToHom_stalk_eq_specializes
    (X : Scheme) {x y : X} (h : x = y) :
    eqToHom (congrArg (fun z => X.presheaf.stalk z) h) =
      X.presheaf.stalkSpecializes (specializes_of_eq h.symm) := by
  subst y
  simp only [eqToHom_refl, TopCat.Presheaf.stalkSpecializes_refl]

/-- The degree used by Riemann--Hurwitz is the degree of the actual
function-field extension of the finite étale scheme cover. -/
theorem finrankAlong_finiteEtaleFieldMap_eq_functionField
    {K F E : Type} [Field K] [IsAlgClosed K]
    [Field F] [Field E] [Algebra K F] [Algebra K E]
    (M : CurveModel K F) (N : CurveModel K E) [IsNormalIntegral M.C]
    (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase) [IsFiniteEtale d] :
    let W : FiniteEtale M.C := FiniteEtale.mk d
    let : ConnectedSpace W.left := inferInstanceAs (ConnectedSpace N.C)
    let : IsConnected W := FiniteEtale.isConnected_of_connectedSpace_left W
    let : Algebra M.C.functionField N.C.functionField := finiteEtaleFunctionFieldAlgebra W
    finrankAlong K (M.finiteEtaleFieldMap N d hd) =
      Module.finrank M.C.functionField N.C.functionField := by
  intro W hconn hW alg
  have : Surjective d := IsFiniteEtale.surjective d
  let phi := M.finiteEtaleFieldMap N d hd
  let : Algebra F E := algebraAlong phi
  have hmap :
      (FFLeg.FunctionFieldPull.pull d
        (FFLeg.specializes_genericPoint K M N d d.surjective)).hom =
      d.functionFieldMap d.surjective.denseRange := by
    unfold FFLeg.FunctionFieldPull.pull Scheme.Hom.functionFieldMap
    rw [eqToHom_stalk_eq_specializes M.C
      (d.map_genericPoint_of_denseRange d.surjective.denseRange).symm]
  change Module.finrank F E = Module.finrank M.C.functionField N.C.functionField
  refine Algebra.finrank_eq_of_equiv_equiv M.ffEquiv N.ffEquiv ?_
  apply RingHom.ext
  intro x
  change d.functionFieldMap d.surjective.denseRange (M.ffEquiv x) = N.ffEquiv (phi x)
  change d.functionFieldMap d.surjective.denseRange (M.ffEquiv x) =
    N.ffEquiv (N.ffEquiv.symm
      (FFLeg.FunctionFieldPull.pull d
        (FFLeg.specializes_genericPoint K M N d d.surjective) (M.ffEquiv x)))
  rw [N.ffEquiv.apply_symm_apply]
  exact (congrArg (fun q : M.C.functionField →+* N.C.functionField =>
    q (M.ffEquiv x)) hmap).symm

end AlgebraicCurve.CurveModel
