/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Pic0.Pic0_exists_injective_conorm_of_constantFieldExtension_of_isAlgClosed
import Nyll.AlgebraicCurves.Divisors.Semilinear

/-!
# Constant-extension divisors are fixed by coefficient actions

Uniqueness of the actual lifted valuation implies that an action fixing
the old function field fixes each lifted old place, and hence its conorm
divisors. The fixed-function-field input is supplied by the geometric
projection square in CurveModel.semilinear_fixes_functionField_image.
-/

noncomputable section

open AlgebraicCurve
open JacobianVarieties.Pic0.Proofs.ConormInjectivity.AlgebraicCurve.ConDesc
open scoped Pointwise

namespace JacobianVarieties.Picard

attribute [local instance]
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor

variable {K F K' F' : Type*}
  [Field K] [Field F] [Field K'] [Field F']
  [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
  [IsScalarTower K K' F'] [IsScalarTower K F F']
  [IsAlgClosed K] [IsCurveOver K F]
  (hfg : ∃ x : F, Transcendental K x ∧
    FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
  (hfg' : ∃ x : F', Transcendental K' x ∧
    FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
  (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
  (σ : SemilinearAut K' F')
  (hfix : ∀ f : F, σ • algebraMap F F' f = algebraMap F F' f)

include hfix in
/-- Coefficient actions fix the unique extension of each original place. -/
theorem constantExtension_place_fixed (v : Place K F) :
    σ • lift hfg hfg' hgen v = lift hfg hfg' hgen v := by
  have hinv (f : F) : σ⁻¹ • algebraMap F F' f = algebraMap F F' f := by
    apply MulAction.injective σ
    change σ • (σ⁻¹ • algebraMap F F' f) = σ • algebraMap F F' f
    rw [smul_inv_smul, hfix]
  apply eq_lift_of_comap_eq hfg hfg' hgen
  rw [← comap_lift hfg hfg' hgen v]
  ext f
  change algebraMap F F' f ∈ (σ • lift hfg hfg' hgen v).toValuationSubring ↔
    algebraMap F F' f ∈ (lift hfg hfg' hgen v).toValuationSubring
  rw [SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hinv]

include hfix in
/-- The same actual coefficient action fixes conorm divisors, not just
their divisor classes. -/
theorem constantExtension_divisor_fixed (D : Divisor K F) :
    σ • con hfg hfg' hgen D = con hfg hfg' hgen D := by
  change σ • Finsupp.mapDomain (lift hfg hfg' hgen) D =
    Finsupp.mapDomain (lift hfg hfg' hgen) D
  rw [SemilinearAut.divisor_smul_def, ← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro v _
  exact constantExtension_place_fixed hfg hfg' hgen σ hfix v

end JacobianVarieties.Picard
