/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.CurveModel_exists_representsRelSubPic_abelJacobi_of_isAlgClosed
import Nyll.JacobianVarieties.Pic0.Pic0_exists_nsmul_eq_of_jacobianPack_of_natCast_ne_zero
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.MultiplicationMorphisms
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_exists_separating_transcendental
import Nyll.AlgebraicCurves.Models.IsCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one

/-!
# Divisibility of the actual degree-zero divisor class group

The curve supplies its Picard scheme and its actual group law. The proved
geometric surjectivity of multiplication then supplies divisibility of
Pic⁰; neither a Jacobian presentation nor divisibility is an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian GoodReductionJacobian.RelativeGroupLaw
open AlgebraicCurves.Models.Proofs
open IsCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one

namespace AlgebraicCurve.CurveModel

/-- Multiplication by an integer invertible in the algebraically closed
constant field is surjective on the actual degree-zero divisor class group. -/
theorem pic0_exists_nsmul_eq
    {K F : Type} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F)
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    (n : ℕ) (hn : n ≠ 0) (hchar : (n : K) ≠ 0) (x : Pic0 K F) :
    ∃ y : Pic0 K F, n • y = x := by
  have : Algebra.EssFiniteType K F := by
    let : Algebra K M.C.functionField := (baseToFunctionField M.toBase).toAlgebra
    let e : F ≃ₐ[K] M.C.functionField :=
      AlgEquiv.ofRingEquiv (f := M.ffEquiv) M.ffEquiv_algebraMap
    exact (Algebra.EssFiniteType.iff_of_algEquiv e).mpr
      (SmoothModelFunctionField.stageA M.toBase).1
  obtain ⟨t, ht, hfin, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  obtain ⟨D, hD, _, hs, hp, hg, _, _, pts, hadd, _⟩ :=
    M.exists_representsRelSubPic_abelJacobi_of_isAlgClosed K F ε
  have : GeometricallyConnected D.toBase := hg
  have hconn : ConnectedSpace D.P :=
    GeometricallyConnected.connectedSpace_of_subsingleton D.toBase
  let G := RepresentsRelSubPic.relativeGroupLaw
    (P := algEquivZeroGroupCut M.toBase ε) hD
  apply Pic0.exists_nsmul_eq_of_jacobianPack_of_natCast_ne_zero
    K F ⟨t, ht, hfin⟩ D.P D.toBase hs hp hconn
    (G.mulRight D.toBase idPoint) pts
    (fun a b => (congrArg Subtype.val (hadd a b)).trans
      (G.pullback_lift_comp_mulRight_idPoint (𝟙 _) (pts a) (pts b)).symm)
    n hn hchar x

end AlgebraicCurve.CurveModel
