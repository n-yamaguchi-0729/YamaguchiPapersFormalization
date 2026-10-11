/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero

/-!
# Rational Function Field trace local Residue place Infty X pow eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs
namespace RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero

open _root_.AlgebraicCurves.Places.Rational.Proofs
open _root_.AlgebraicCurve.Place.CanonicalLocalResidueDataK

theorem _root_.AlgebraicCurve.RationalFunctionField.trace_localResidue_placeInfty_X_pow_eq_zero
    (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K (RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    (n : ℕ) :
    Algebra.trace K (AlgebraicCurve.RationalFunctionField.placeInfty K).ResidueField
        ((AlgebraicCurve.RationalFunctionField.placeInfty K).localResidue
          ((RatFunc.X : RatFunc K) ^ n
            * (AlgebraicCurve.RationalFunctionField.placeInfty K).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)))) = 0 := by
  let v := AlgebraicCurve.RationalFunctionField.placeInfty K
  have hD :
      v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) RatFunc.X)
        = (-(RatFunc.X : RatFunc K) ^ 2) *
            v.differentialCoeff
              (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹) := by
    rw [show KaehlerDifferential.D K (RatFunc K) RatFunc.X
        = (-(RatFunc.X : RatFunc K) ^ 2) •
            KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹ from
      (KaehlerDifferential.D K (RatFunc K)).leibniz_of_mul_eq_one
        (mul_inv_cancel₀ RatFunc.X_ne_zero),
      v.differentialCoeff_smul]
  have hinvPow (m : ℕ) :
      (((RatFunc.X : RatFunc K)⁻¹) ^ m)⁻¹ = (RatFunc.X : RatFunc K) ^ m := by
    rw [inv_pow, inv_inv]
  have hrewrite :
      (RatFunc.X : RatFunc K) ^ n
          * v.differentialCoeff
              (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K))
        = -(v.differentialCoeff
              (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)
            * (((RatFunc.X : RatFunc K)⁻¹) ^ (n + 2))⁻¹) := by
    rw [hD, hinvPow]
    ring
  have hzero :
      (AlgebraicCurve.HasCanonicalLocalResidueKStar.dataKStar v).res
        (v.differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)
          * (((RatFunc.X : RatFunc K)⁻¹) ^ (n + 2))⁻¹) = 0 := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap
        v
        (FinitePlaceResidueTrace.AlgebraicCurve.surjective_algebraMap_residueField_placeInfty K)
        (fun h hh => by
          open FinitePlaceResidueTrace.AlgebraicCurve in
          exact ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField v hh)
        (AlgebraicCurve.HasCanonicalLocalResidueKStar.dataKStar v)
        (FinitePlaceResidueTrace.AlgebraicCurve.ord_placeInfty_X_inv K)
        (n := n + 1) (by omega))
  have hres :
      v.localResidue
        ((RatFunc.X : RatFunc K) ^ n
          * v.differentialCoeff
              (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K))) = 0 := by
    change (AlgebraicCurve.HasCanonicalLocalResidueKStar.dataKStar v).res _ = 0
    rw [hrewrite, map_neg, hzero, neg_zero]
  change Algebra.trace K v.ResidueField (v.localResidue _) = 0
  rw [hres, map_zero]

end RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero
end AlgebraicCurves.Places.Rational.Proofs
end ProofImplementation
