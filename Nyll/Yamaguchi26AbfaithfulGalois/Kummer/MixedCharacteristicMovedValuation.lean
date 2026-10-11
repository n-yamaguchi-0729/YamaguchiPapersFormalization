/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.ValuationCharacterDetection
import Nyll.GaloisCohomology.Kummer.Concrete.MixedCharacteristicCharacters
import Nyll.ValuedFieldTheory.Valuation.Completion.DiscreteValuedCompletion

/-!
# Detecting an automorphism which moves a discrete valuation

A nonzero residue-prime character of one completion and the zero character
of its inequivalent conjugate extend simultaneously by weak approximation.
Their different values detect the relative action on abelianization modulo
the residue prime.
-/

namespace Yamaguchi26AbfaithfulGalois
open KummerTheory ValuationTheory.DiscreteValuationField ProCGroups.Abelian
open Field.absoluteGaloisGroup
universe u v

/-- Moving a mixed-characteristic discrete valuation forces a nontrivial
action on the absolute Galois abelianization modulo the residue prime. -/
theorem exists_moved_mod_prime_of_moved_valuation
    {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero L]
    (target : DVF.{u, v} L) (p : ℕ) [Fact p.Prime] [CharP target.residueField p]
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
  let targetHat : DVF.{u,v} (D 0).valuation.Completion :=
    { ValueGroup := (D 0).ValueGroup
      valuation := Valued.v
      instRankOneDiscrete := Valuation.completion_isRankOneDiscrete (D 0).valuation }
  have : CharP (D 0).residueField p := inferInstanceAs (CharP target.residueField p)
  have : CharP targetHat.residueField p := Valuation.completion_residueChar (D 0).valuation p
  have : CharZero (D 0).valuation.Completion :=
    charZero_of_injective_algebraMap (algebraMap L (D 0).valuation.Completion).injective
  obtain ⟨χ, hχ⟩ := exists_surjective_prime_character_of_mixedChar targetHat p
  obtain ⟨a, ha⟩ := hχ (Multiplicative.ofAdd (1 : ZMod p))
  have ha' : χ a ≠ 1 := by
    rw [ha]
    intro h
    exact (one_ne_zero : (1 : ZMod p) ≠ 0)
      (congrArg (fun x : Multiplicative (ZMod p) => x.toAdd) h)
  exact exists_moved_mod_prime_of_inequivalent_completions D hD p τ
    (fun _ _ => Iff.rfl) χ a ha'
end Yamaguchi26AbfaithfulGalois
