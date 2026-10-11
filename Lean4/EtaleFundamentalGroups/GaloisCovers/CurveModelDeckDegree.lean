/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.CurveModelDegree
import AlgebraicCurves.Models.FiniteEtaleHyperbolicGenus

/-! # Nonidentity actual deck transformations force degree greater than one -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups

namespace AlgebraicCurve.CurveModel

/-- A nonidentity actual deck transformation supplies the strict degree
inequality needed by the geometric H¹ cardinality argument. -/
theorem one_lt_finrankAlong_of_nontrivial_deck
    {K F E : Type} [Field K] [IsAlgClosed K]
    [Field F] [Field E] [Algebra K F] [Algebra K E]
    (M : CurveModel K F) (N : CurveModel K E) [IsNormalIntegral M.C]
    (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase) [IsFiniteEtale d]
    (σ : Aut (FiniteEtale.mk d)) (hne : σ ≠ 1) :
    1 < finrankAlong K (M.finiteEtaleFieldMap N d hd) := by
  have : IsLocallyNoetherian M.C :=
    LocallyOfFiniteType.isLocallyNoetherian M.toBase
  let W : FiniteEtale M.C := FiniteEtale.mk d
  have : ConnectedSpace W.left := inferInstanceAs (ConnectedSpace N.C)
  have : IsConnected W := FiniteEtale.isConnected_of_connectedSpace_left W
  let : Algebra M.C.functionField N.C.functionField := finiteEtaleFunctionFieldAlgebra W
  have he := M.finrankAlong_finiteEtaleFieldMap_eq_functionField N d hd
  have : FiniteDimensional M.C.functionField N.C.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  have hc : Nat.card (Aut W) ≤ finrankAlong K (M.finiteEtaleFieldMap N d hd) := calc
    Nat.card (Aut W) ≤
        Nat.card (N.C.functionField ≃ₐ[M.C.functionField] N.C.functionField) :=
      Nat.card_le_card_of_injective
        (finiteEtaleAutFunctionFieldAlgEquiv W)
        (finiteEtaleAutFunctionFieldAlgEquiv_injective W)
    _ = Nat.card (N.C.functionField →ₐ[M.C.functionField] N.C.functionField) :=
      Nat.card_congr (algEquivEquivAlgHom M.C.functionField N.C.functionField)
    _ ≤ Module.finrank M.C.functionField N.C.functionField :=
      card_algHom_le_finrank M.C.functionField N.C.functionField N.C.functionField
    _ = finrankAlong K (M.finiteEtaleFieldMap N d hd) := he.symm
  have hp := M.finrankAlong_finiteEtaleFieldMap_pos N d hd
  by_contra hn
  have hdegree : finrankAlong K (M.finiteEtaleFieldMap N d hd) = 1 :=
    Nat.le_antisymm (Nat.le_of_not_gt hn) (Nat.succ_le_of_lt hp)
  have hcOne : Nat.card (Aut W) = 1 :=
    Nat.le_antisymm (hc.trans_eq hdegree) (Nat.succ_le_of_lt Nat.card_pos)
  have hs := (Nat.card_eq_one_iff_unique.mp hcOne).1
  exact hne (hs.elim σ 1)

end AlgebraicCurve.CurveModel
