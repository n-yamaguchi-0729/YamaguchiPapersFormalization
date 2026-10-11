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
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Is Integral adjoin map alg Hom
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.IsIntegral_adjoin_map_algHom

theorem _root_.AlgebraicCurve.isIntegral_adjoin_map_algHom {K F F' : Type*} [CommRing K] [CommRing
  F] [CommRing F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') {j x : F} (hx : IsIntegral
  (Algebra.adjoin K {j}) x) : IsIntegral (Algebra.adjoin K {φ j}) (φ x) := by
  have hle : (Algebra.adjoin K {j}).map φ ≤ Algebra.adjoin K {φ j} := by
    rw [Subalgebra.map_le]
    refine Algebra.adjoin_le fun y hy => ?_
    rw [Set.mem_singleton_iff.mp hy]
    change j ∈ Subalgebra.comap φ (Algebra.adjoin K {φ j})
    rw [Subalgebra.mem_comap]
    exact Algebra.subset_adjoin rfl
  have hmem : ∀ a : ↥(Algebra.adjoin K {j}),
      (φ.comp (Algebra.adjoin K {j}).val) a ∈ Algebra.adjoin K {φ j} :=
    fun a => hle (Subalgebra.mem_map.mpr ⟨(a : F), a.2, rfl⟩)
  have key := IsIntegral.map_of_comp_eq
    ((φ.comp (Algebra.adjoin K {j}).val).codRestrict (Algebra.adjoin K {φ j}) hmem).toRingHom
    φ.toRingHom (by ext a; rfl) hx
  exact key
end AlgebraicCurves.FunctionFields.Proofs.IsIntegral_adjoin_map_algHom
end ProofImplementation
