/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.RelativeAbelianModPowerAction
import Nyll.ProCGroups.Abelian.PrimeExponentCharacters
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Detecting cohomology actions from moved mod-prime classes

A moved mod-prime abelianization class yields a nontrivial relative Galois
cohomology action. The inverse automorphism reflects contravariant pullback.
-/

namespace Yamaguchi26AbfaithfulGalois

open KummerTheory ProCGroups.Abelian ClassFieldTower.ProP

universe u

/-- A moved mod-prime abelianization class gives a nontrivial action on H¹.
The inverse appears because the cohomology action uses inverse pullback. -/
theorem inverse_relativeH1Action_ne_one_of_moved_abelianModPower
    (K L : Type u) [Field K] [Field L] [Algebra K L] [CharZero L]
    (p : ℕ) [Fact p.Prime] (τ : Gal(L/K))
    (z : abelianModPower Gal(AlgebraicClosure L/L) p)
    (hz : relativeGaloisAbelianModPowerTransform K L p τ z ≠ z) :
    relativeGaloisH1Action (n := p) K L τ⁻¹ ≠ 1 := by
  have hdiff : relativeGaloisAbelianModPowerTransform K L p τ z * z⁻¹ ≠ 1 :=
    fun h => hz (mul_inv_eq_one.mp h)
  obtain ⟨χ, hχ⟩ := exists_prime_character_abelianModPower hdiff
  obtain ⟨σ, rfl⟩ := abelianModPowerMk_surjective (G := Gal(AlgebraicClosure L/L)) p z
  let ψ := χ.comp (abelianModPowerMk Gal(AlgebraicClosure L/L) p)
  intro htrivial
  have heq := congrArg (fun e => e.toAdd (h1OfCharacter ψ)
    (Additive.ofMul (σ : Field.absoluteGaloisGroup L))) htrivial
  have hvalue : ψ (absoluteGaloisConjugate τ.toRingEquiv σ) = ψ σ :=
    Multiplicative.toAdd.injective heq
  apply hχ
  rw [map_mul, map_inv, show χ (relativeGaloisAbelianModPowerTransform K L p τ
    (abelianModPowerMk Gal(AlgebraicClosure L/L) p σ)) =
      χ (abelianModPowerMk Gal(AlgebraicClosure L/L) p σ) from hvalue,
    mul_inv_cancel]

end Yamaguchi26AbfaithfulGalois
