/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.PositiveCharacteristic
import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.PadicQuotient
import Nyll.GaloisCohomology.ArtinSchreier.NontrivialCharacter
import Nyll.GaloisCohomology.ProfiniteIntegers.PadicPrincipalUnitPowers
import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosureAutTopology

/-! # Infinite orientations from Artin–Schreier obstructions -/

namespace Yamaguchi26AbfaithfulGalois
universe u

/-- A nontrivial mod-p character lifts to an infinite principal-unit orientation. -/
theorem exists_infinite_formalHilbert90_orientation_of_character
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p]
    (χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod p))
    (hχ : ∃ σ : Gal(AlgebraicClosure K/K), χ σ ≠ 1) :
    ∃ θ : Orientation p Gal(AlgebraicClosure K/K),
      FormalHilbert90 θ ∧ Set.Infinite (Set.range θ) := by
  have hF : FormalHilbert90 (1 : Orientation p Gal(AlgebraicClosure K/K)) := by
    apply formalHilbert90_absolute_of_charP p K
    intro σ
    rw [ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, map_one]
  obtain ⟨ν, hν⟩ := exists_surjective_padic_character_of_formalHilbert90_trivial hF χ hχ
  obtain ⟨φ, hφ, hmod⟩ := PadicInt.exists_infinite_principal_unit_character p
  let θ : Orientation p Gal(AlgebraicClosure K/K) := φ.comp ν
  refine ⟨θ, formalHilbert90_absolute_of_charP p K θ (fun σ => hmod (ν σ)), ?_⟩
  apply hφ.mono
  rintro y ⟨x, rfl⟩
  obtain ⟨σ, rfl⟩ := hν x
  exact ⟨σ, rfl⟩


/-- A nonsurjective Artin–Schreier map supplies an infinite orientation with
formal Hilbert 90 on the actual absolute Galois group, including imperfect fields. -/
theorem exists_infinite_formalHilbert90_orientation_of_artinSchreier
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p]
    (hAS : ∃ a : K, ∀ x : K, x ^ p - x ≠ a) :
    ∃ θ : Orientation p Gal(AlgebraicClosure K/K),
      FormalHilbert90 θ ∧ Set.Infinite (Set.range θ) := by
  obtain ⟨χsep, σsep, hσsep⟩ :=
    ArtinSchreierTheory.exists_nontrivial_character_of_artinSchreier_not_surjective
      p (K := K) (Ω := SeparableClosure K) hAS
  let e := ValuationTheory.Completion.separableClosureAutContinuousEquiv K
  let χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod p) :=
    χsep.comp (e : Gal(AlgebraicClosure K/K) →ₜ* Gal(SeparableClosure K/K))
  have hχ : ∃ σ : Gal(AlgebraicClosure K/K), χ σ ≠ 1 := by
    obtain ⟨σ, hσ⟩ := e.surjective σsep
    exact ⟨σ, by change χsep (e σ) ≠ 1; rw [hσ]; exact hσsep⟩
  exact exists_infinite_formalHilbert90_orientation_of_character p K χ hχ

end Yamaguchi26AbfaithfulGalois
