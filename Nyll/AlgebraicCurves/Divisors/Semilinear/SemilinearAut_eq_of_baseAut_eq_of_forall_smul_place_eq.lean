/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_SemilinearAut_eq_of_baseAut_eq_of_forall_smul_place_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Divisors.Semilinear
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Places.AlgEquiv_eq_one_of_forall_smul_place_eq
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_ofAlgAut_smul_place

/-!
# Semilinear Aut eq of base Aut eq of forall smul place eq
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Semilinear.Proofs
namespace SemilinearAut_eq_of_baseAut_eq_of_forall_smul_place_eq
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

universe u v

open AlgebraicCurve

namespace QForm1b

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

/--
The algebra automorphism underlying a semilinear automorphism whose base automorphism is the
identity.
-/
noncomputable def algEquivOfBaseAutEqOne (k : SemilinearAut K F) (hk : SemilinearAut.baseAut k = 1)
  :
    F ≃ₐ[K] F :=
  AlgEquiv.ofRingEquiv (f := SemilinearAut.toRingAut k) fun a => by
    rw [SemilinearAut.commutes k a, hk]
    rfl

theorem ofAlgAut_algEquivOfBaseAutEqOne (k : SemilinearAut K F) (hk : SemilinearAut.baseAut k = 1) :
    SemilinearAut.ofAlgAut (algEquivOfBaseAutEqOne k hk) = k := by
  apply Subtype.ext
  apply Prod.ext
  · exact RingEquiv.ext fun _ => rfl
  · exact hk.symm

end QForm1b

open QForm1b in
theorem solution
    {K : Type u} {F : Type v} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Algebra.EssFiniteType K F]
    (g g' : SemilinearAut K F) (hb : SemilinearAut.baseAut g = SemilinearAut.baseAut g')
    (h : ∀ v : Place K F, g • v = g' • v) : g = g' := by
  set k : SemilinearAut K F := g⁻¹ * g' with hkdef
  have hk : SemilinearAut.baseAut k = 1 := by
    rw [hkdef, SemilinearAut.baseAut_mul, SemilinearAut.baseAut_inv, hb]
    exact inv_mul_cancel (SemilinearAut.baseAut g')
  have hkv : ∀ v : Place K F, k • v = v := fun v => by
    rw [hkdef, mul_smul, ← h v, inv_smul_smul]
  have hσv : ∀ v : Place K F, algEquivOfBaseAutEqOne k hk • v = v := fun v => by
    rw [← SemilinearAut.ofAlgAut_smul_place, ofAlgAut_algEquivOfBaseAutEqOne k hk, hkv v]
  have hσ1 : algEquivOfBaseAutEqOne k hk = 1 :=
    AlgebraicCurve.AlgEquiv.eq_one_of_forall_smul_place_eq _ hσv
  have hk1 : k = 1 := by
    rw [← ofAlgAut_algEquivOfBaseAutEqOne k hk, hσ1, map_one]
  exact inv_mul_eq_one.1 hk1

end SemilinearAut_eq_of_baseAut_eq_of_forall_smul_place_eq
end AlgebraicCurves.Divisors.Semilinear.Proofs
end ProofImplementation


attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve

universe u v

open AlgebraicCurves.Divisors.Semilinear.Proofs in
open SemilinearAut_eq_of_baseAut_eq_of_forall_smul_place_eq
  renaming solution → semilinearProof in
theorem AlgebraicCurve.SemilinearAut.eq_of_baseAut_eq_of_forall_smul_place_eq
    {K : Type u} {F : Type v} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Algebra.EssFiniteType K F]
    (g g' : SemilinearAut K F) (hb : SemilinearAut.baseAut g = SemilinearAut.baseAut g')
    (h : ∀ v : Place K F, g • v = g' • v) : g = g' := by
  exact semilinearProof (K := K) (F := F) (g := g) (g' := g') (hb := hb) (h := h)
