/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FinitelyGeneratedMovingValuation
import Nyll.GaloisCohomology.ArtinSchreier.ValuationCharacters
import Nyll.GaloisCohomology.FieldTheory.FinitelyGeneratedExtensions
import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.ValuationCharacterDetection

/-!
# Detecting Galois automorphisms over finitely generated fields of positive characteristic

Nontrivial finite-order automorphisms move discrete valuations. A local
Artin--Schreier character and weak approximation detect their action modulo
the characteristic, including over imperfect fields.
-/

namespace Yamaguchi26AbfaithfulGalois
open ValuationTheory.DiscreteValuationField ProCGroups.Abelian
universe u v

/-- Moving a discrete valuation in characteristic `p` forces a nontrivial
modulo-`p` action on absolute Galois abelianization. -/
theorem exists_moved_mod_prime_of_moved_valuation_posChar
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (target : DVF.{u, v} L) (p : ℕ) [Fact p.Prime] [CharP L p]
    (τ : Gal(L/K))
    (hτ : ¬ target.valuation.IsEquiv (target.valuation.comap τ.toRingEquiv.toRingHom)) :
    ∃ z : abelianModPower Gal(AlgebraicClosure L/L) p,
      relativeGaloisAbelianModPowerTransform K L p τ.symm z ≠ z := by
  classical
  let moved : DVF.{u,v} L :=
    { ValueGroup := target.ValueGroup
      valuation := target.valuation.comap τ.toRingEquiv.toRingHom
      instRankOneDiscrete := Valuation.isRankOneDiscrete_comap_ringEquiv
        target.valuation τ.toRingEquiv }
  let D : Fin 2 → DVF.{u,v} L := ![target, moved]
  have hD : Pairwise (fun i j => ¬ (D i).valuation.IsEquiv (D j).valuation) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hτ
    · intro h
      exact hτ h.symm
    · exact False.elim (hij rfl)
  obtain ⟨χ, a, ha⟩ :=
    ArtinSchreierTheory.exists_nontrivial_completion_character_of_DVF (D 0) p
  exact exists_moved_mod_prime_of_inequivalent_completions D hD p τ
    (fun _ _ => Iff.rfl) χ a ha

/-- Prime-degree Galois extensions of infinite finitely generated fields in
positive characteristic act nontrivially on absolute abelianization modulo
that characteristic. -/
theorem prime_order_detection_of_fg_posChar
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (p r : ℕ) [Fact p.Prime] [Fact r.Prime] [CharP K p] [Infinite K]
    (hfg : Field.FG K) (hdegree : Module.finrank K L = r) :
    ∃ τ : Gal(L/K), τ ≠ 1 ∧
      ∃ z : abelianModPower Gal(AlgebraicClosure L/L) p,
        relativeGaloisAbelianModPowerTransform K L p τ z ≠ z := by
  classical
  have : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (hdegree.symm ▸ (Fact.out : r.Prime).pos)
  have : CharP L p := charP_of_injective_ringHom (algebraMap K L).injective p
  have : Infinite L := Infinite.of_injective (algebraMap K L) (algebraMap K L).injective
  have hcard : Nat.card Gal(L/K) = r := (IsGalois.card_aut_eq_finrank K L).trans hdegree
  have : Nontrivial Gal(L/K) := Finite.one_lt_card_iff_nontrivial.mp
    (hcard.symm ▸ (Fact.out : r.Prime).one_lt)
  obtain ⟨τ, hτ⟩ := exists_ne (1 : Gal(L/K))
  let φ : Gal(L/K) →* RingAut L :=
    { toFun := AlgEquiv.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hne : φ τ ≠ 1 := by
    intro h
    apply hτ
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun h x
  have hpow : (φ τ) ^ orderOf τ = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  obtain ⟨D, hD⟩ := FieldTheory.exists_moved_DVF_of_fg_posChar L
    (FieldTheory.fg_of_finiteDimensional K L hfg)
    ((ringChar.eq L p).trans_ne (Fact.out : p.Prime).ne_zero)
    (φ τ) hne (orderOf τ) (orderOf_pos τ) hpow
  exact ⟨τ.symm, inv_ne_one.mpr hτ,
    exists_moved_mod_prime_of_moved_valuation_posChar D p τ hD⟩
end Yamaguchi26AbfaithfulGalois
