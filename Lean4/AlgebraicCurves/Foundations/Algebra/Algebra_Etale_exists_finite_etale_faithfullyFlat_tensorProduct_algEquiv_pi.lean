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

import AlgebraicCurves.Foundations.Algebra.Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq

/-!
# Algebra Etale exists finite etale faithfully Flat tensor Product alg Equiv pi
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi

open scoped TensorProduct

universe u

theorem _root_.Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.Etale R B] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R')
      (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R') (_ : IsNoetherianRing R'),
      Nonempty ((R' ⊗[R] B) ≃ₐ[R'] (Fin (Module.finrank R B) → R')) := by
  let _ : Module.Free R B := Module.free_of_flat_of_isLocalRing
  obtain ⟨R', _, _, _, _, _, ⟨e⟩⟩ :=
    Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq R B
      (Module.finrank R B) (fun p => by rw [Module.rankAtStalk_eq_finrank_of_free]; rfl)
  exact ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Algebra.FiniteType.isNoetherianRing R R', ⟨e⟩⟩
end Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
