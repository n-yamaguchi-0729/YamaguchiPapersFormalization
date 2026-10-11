/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.Kummer.RelativeAbelianModPowerAction
import GaloisCohomology.ArtinSchreier.AutomorphismDetection
import GaloisCohomology.ArtinSchreier.PrimeDegreeAction
import GaloisCohomology.Kummer.Concrete.AbsoluteRestrictionConjugation
import ValuedFieldTheory.Valuation.DiscreteValuationField.ArtinSchreierPrimeToDegree
import ValuedFieldTheory.Valuation.DiscreteValuationField.PolynomialImageInfinite
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Prime-degree detection over complete discretely valued fields of characteristic p

Artin--Schreier classes are infinite over a discretely valued field. In degree p,
finite restriction kernels and additive Hilbert 90 detect the action. In every
other prime degree, a norm valuation and a base-field multiple detect it directly.
-/

namespace Yamaguchi26AbfaithfulGalois

open KummerTheory ProCGroups.Abelian ValuationTheory.DiscreteValuationField

universe u v

/-- A moved Artin--Schreier class detects the actual relative action modulo p. -/
theorem exists_moved_mod_prime_of_artinSchreier_difference
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP L p] (τ : Gal(L/K))
    (x : L) (hx : ∀ y : L, y ^ p - y ≠ τ x - x) :
    ∃ z : abelianModPower Gal(AlgebraicClosure L/L) p,
      relativeGaloisAbelianModPowerTransform K L p τ.symm z ≠ z := by
  obtain ⟨χ, σ, hχ⟩ :=
    ArtinSchreierTheory.exists_character_moved_by_map_of_pow_sub_ne p τ.toRingEquiv x hx
  refine ⟨abelianModPowerMk _ p σ, ?_⟩
  intro hfixed
  have hpow : ∀ a : Multiplicative (ZMod p), a ^ p = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    change p • a.toAdd = (0 : ZMod p)
    simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have h := congrArg (abelianModPowerLift p χ hpow) hfixed
  change χ (absoluteGaloisConjugate τ.symm.toRingEquiv σ) = χ σ at h
  apply hχ
  exact (character_map_symm_eq_absoluteGaloisConjugate τ.symm.toRingEquiv χ σ).trans h

/-- Every prime-degree Galois extension of a complete discretely valued field
of characteristic p acts nontrivially on its absolute abelianization modulo p. -/
theorem prime_order_detection_of_complete_charP
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (p r : ℕ) [Fact p.Prime] [Fact r.Prime] [CharP K p]
    (D : CompleteDVF.{u, v} K) (hdegree : Module.finrank K L = r) :
    ∃ τ : Gal(L/K), τ ≠ 1 ∧
      ∃ z : abelianModPower Gal(AlgebraicClosure L/L) p,
        relativeGaloisAbelianModPowerTransform K L p τ z ≠ z := by
  classical
  have : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (hdegree.symm ▸ (Fact.out : r.Prime).pos)
  have : CharP L p := charP_of_injective_ringHom (algebraMap K L).injective p
  have hmoved : ∃ τ : Gal(L/K), τ ≠ 1 ∧ ∃ x : L,
      ∀ y : L, y ^ p - y ≠ τ x - x := by
    by_cases hrp : r = p
    · have : Infinite (K ⧸ ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range) :=
        D.toDVF.infinite_artinSchreier_quotient p
      exact ArtinSchreierTheory.exists_moved_class_of_degree_eq_char p (hdegree.trans hrp)
    · have hcard : Nat.card Gal(L/K) = r :=
        (IsGalois.card_aut_eq_finrank K L).trans hdegree
      have : Nontrivial Gal(L/K) := Finite.one_lt_card_iff_nontrivial.mp
        (hcard.symm ▸ (Fact.out : r.Prime).one_lt)
      obtain ⟨τ, hτ⟩ := exists_ne (1 : Gal(L/K))
      have hpd : ¬ p ∣ Module.finrank K L := by
        rw [hdegree]
        intro h
        exact hrp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
          (Fact.out : r.Prime)).mp h).symm
      obtain ⟨x, hx⟩ := D.exists_moved_pow_sub_class_of_not_dvd_finrank
        p (Fact.out : p.Prime).one_lt hpd τ hτ
      exact ⟨τ, hτ, x, hx⟩
  obtain ⟨τ, hτ, x, hx⟩ := hmoved
  exact ⟨τ.symm, inv_ne_one.mpr hτ,
    exists_moved_mod_prime_of_artinSchreier_difference p τ x hx⟩

end Yamaguchi26AbfaithfulGalois
