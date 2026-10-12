/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.WeilPairing.DivisorialWeilPairingData_toHom_injective_of_divisible_coprime_of_isAlgClosed
import Nyll.JacobianVarieties.Pic0.Pic0_exists_zsmul_eq_of_finiteDimensional_ratFunc_of_forall_pow_eq_self
import Nyll.JacobianVarieties.Pic0.Pic0_nonempty_divisorialWeilPairingData_of_isAlgClosed
import Nyll.AlgebraicCurves.FunctionFields.FunctionField_exists_ratFuncAlgHom_apply_X_eq

/-!
# Nondegeneracy of the divisorial Weil pairing in characteristic zero

The divisibility input in the existing Kummer detection proof is supplied
by the proved geometric Jacobian construction and multiplication
surjectivity, for every finite rational-function-field extension.
No divisibility or nondegeneracy hypothesis is left to the caller.
-/

noncomputable section

open AlgebraicCurve

namespace AlgebraicCurve.DivisorialWeilPairingData

/-- In characteristic zero the actual divisorial Weil pairing is
nondegenerate. The auxiliary divisibility of Picard groups is proved by
the existing Jacobian construction, rather than assumed. -/
theorem toHom_injective_charZero
    {K F : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {n : ℕ} [NeZero n] (w : DivisorialWeilPairingData K F n) :
    Function.Injective w.toHom := by
  obtain ⟨x, hx, hfin⟩ := hfg
  have hxrange : x ∉ Set.range (algebraMap K F) := by
    rintro ⟨a, rfl⟩
    exact hx (isAlgebraic_algebraMap a)
  obtain ⟨φ, hφ⟩ := FunctionField.exists_ratFuncAlgHom_apply_X_eq hxrange
  let : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  have : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  have : FiniteDimensional (RatFunc K) F :=
    JacobianVarieties.Pic0.Proofs.ClosedFieldWeilData.AlgebraicCurve.WC7P.finite_ratFunc_of_adjoin
      φ hφ hfin
  apply w.toHom_injective_of_divisible_coprime_of_isAlgClosed
    (Nat.cast_ne_zero.mpr (NeZero.ne n))
  intro L _ _ _ _ _
  exact Pic0.exists_zsmul_eq_of_finiteDimensional_ratFunc_of_forall_pow_eq_self K 1
    (fun a => ⟨1, Nat.zero_lt_one, by simp only [pow_one]⟩) L

end AlgebraicCurve.DivisorialWeilPairingData
