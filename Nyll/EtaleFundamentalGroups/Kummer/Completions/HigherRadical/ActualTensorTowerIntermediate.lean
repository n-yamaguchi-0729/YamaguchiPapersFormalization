/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualTensor.TowerPrescribedExponent

/-!
# Prescribed-root tensor towers with an identified intermediate component

The completed normalization machinery first fixes an intermediate tensor
component.  The post-root tensor tower instead starts from a final component
and contracts it.  This file accepts the equality between those two ideals
and transports the complete target across it internally.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK₀ uK uV uF uL uW

/-- The arbitrary-exponent fixed-component theorem with an explicit
identification of its contracted component. -/
theorem
    integralClosure_pureRadicalFractionField_fixedTensorComponent_etale_of_intermediateIdeal_eq
    {K₀ : Type uK₀} {K : Type uK} {F : Type uF} {L : Type uL}
    [Field K₀] [Field K] [Field F] [Field L]
    [Algebra K₀ K] [Algebra K₀ L]
    [Algebra K F] [FiniteDimensional K F]
    (base : CompleteDVF.{uK, uV} K)
    [CharZero base.residueField]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (N : ℕ) (hN : 0 < N)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra base.valuationSubring F]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower base.valuationSubring K F]
    [Algebra K₀ F] [IsScalarTower K₀ K F]
    (m : Ideal (F ⊗[K₀] L)) (hm : m.IsMaximal)
    (n : Ideal (K ⊗[K₀] L)) (hn : n.IsMaximal)
    (hmn : genericTensorTowerIntermediateIdeal
      (K := K₀) (F := K) (F' := F) (L := L) m = n)
    (target : CompleteDVF.{max uK uL, uW}
      (GenericTensorFieldComponent n))
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (hdiv : ramificationIndex base.toDVF target.toDVF ∣ N) :
    let Rn := AdjoinRoot (X ^ N - C varpi)
    let P := GenericTensorFieldComponent m
    letI : Algebra Rn P :=
      genericTensorFieldComponentLeftScalarAlgebra (R := Rn) m
    Algebra.Etale Rn (integralClosure Rn P) := by
  let : m.IsMaximal := hm
  let : n.IsMaximal := hn
  subst n
  exact
    integralClosure_pureRadicalFractionField_fixedTensorComponent_etale_of_completeTarget
      base varpi hvarpi N hN m hm target hdiv

end EtaleFundamentalGroups.Kummer

end
