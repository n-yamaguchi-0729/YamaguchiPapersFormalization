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

import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-!
# Is Integral adjoin of is Scalar Tower
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.IsIntegral_adjoin_of_isScalarTower

theorem _root_.AlgebraicCurve.isIntegral_adjoin_of_isScalarTower {K L F : Type*} [CommRing K]
  [CommRing L] [CommRing F] [Algebra K L] [Algebra K F] [Algebra L F] [IsScalarTower K L F] {j x :
  F} (hx : IsIntegral (Algebra.adjoin K {j}) x) : IsIntegral (Algebra.adjoin L {j}) x := by
  have hsub : Algebra.adjoin K {j} ≤ Subalgebra.restrictScalars K (Algebra.adjoin L {j}) :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr
      ((Subalgebra.mem_restrictScalars K).mpr (Algebra.subset_adjoin rfl)))
  let φ' : ↥(Algebra.adjoin K {j}) →+* ↥(Algebra.adjoin L {j}) :=
    { toFun := fun a => ⟨(a : F), (Subalgebra.mem_restrictScalars K).mp (hsub a.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact IsIntegral.map_of_comp_eq φ' (RingHom.id F) (by ext a; rfl) hx
end AlgebraicCurves.FunctionFields.Proofs.IsIntegral_adjoin_of_isScalarTower
end ProofImplementation
