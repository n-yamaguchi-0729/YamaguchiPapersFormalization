/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Yamaguchi26AbfaithfulGalois.Kummer.MixedCharacteristicCompletionDetection
import Yamaguchi26AbfaithfulGalois.Kummer.MixedCharacteristicMovedValuation
import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.ProlongationDiscrete

/-!
# Prime-degree detection for arbitrary mixed-characteristic discrete valuations

A prolongation is either invariant under every automorphism or is moved by
one. Completion detects the first case, and simultaneous character approximation
detects the second case. No completeness or Henselian hypothesis is required.
-/

namespace Yamaguchi26AbfaithfulGalois
open ValuationTheory.DiscreteValuationField ProCGroups.Abelian
universe u v

/-- Prime-degree Galois extensions of a mixed-characteristic discretely valued
field act nontrivially on abelianization modulo the residue prime. -/
theorem prime_order_detection_of_mixedChar
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [CharZero K] (base : DVF.{u, v} K)
    (p r : ℕ) [Fact p.Prime] [Fact r.Prime] [CharP base.residueField p]
    (hdegree : Module.finrank K L = r) :
    ∃ τ : Gal(L/K), τ ≠ 1 ∧
      ∃ z : abelianModPower Gal(AlgebraicClosure L/L) p,
        relativeGaloisAbelianModPowerTransform K L p τ z ≠ z := by
  classical
  have : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (hdegree.symm ▸ (Fact.out : r.Prime).pos)
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  obtain ⟨target, htarget, hres⟩ := base.exists_extension_residueChar (L := L) p
  have : base.valuation.HasExtension target.valuation := htarget
  have : CharP target.residueField p := hres
  by_cases hstable : ∀ τ : Gal(L/K),
      target.valuation.IsEquiv (target.valuation.comap τ.toRingEquiv.toRingHom)
  · exact prime_order_detection_of_stable_valuation base target p r hdegree hstable
  · obtain ⟨τ, hτ⟩ := not_forall.mp hstable
    have hne : τ ≠ 1 := by
      intro heq
      apply hτ
      intro x y
      change target.valuation x ≤ target.valuation y ↔
        target.valuation (τ x) ≤ target.valuation (τ y)
      rw [heq]
      rfl
    exact ⟨τ.symm, inv_ne_one.mpr hne,
      exists_moved_mod_prime_of_moved_valuation target p τ hτ⟩
end Yamaguchi26AbfaithfulGalois
