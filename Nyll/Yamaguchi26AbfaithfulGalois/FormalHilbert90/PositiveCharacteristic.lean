/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.TwoCocycleLifting
import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.Equivalence
import Nyll.GaloisCohomology.ArtinSchreier.OpenCohomologyVanishing
import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosureAutTopology

/-! # Formal Hilbert 90 in positive characteristic -/

namespace Yamaguchi26AbfaithfulGalois
universe u v
variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]

/-- In characteristic `p`, every orientation trivial modulo `p` satisfies
formal Hilbert 90 on a separably closed Galois extension. -/
theorem formalHilbert90_galois_of_charP
    [IsGalois K Ω] [IsSepClosed Ω] [CharP Ω p]
    (θ : Orientation p Gal(Ω/K))
    (hθ : ∀ g : Gal(Ω/K), PadicInt.toZModPow 1 (θ g : PadicInt p) = 1) :
    FormalHilbert90 θ :=
  formalHilbert90_of_twoCocycles θ hθ
    (ArtinSchreierTheory.exists_zmod_primitive_of_two_cocycle_open p)

/-- Formal Hilbert 90 in characteristic `p` on the actual algebraic-closure
Galois group, including imperfect base fields. -/
theorem formalHilbert90_absolute_of_charP [CharP K p]
    (θ : Orientation p Gal(AlgebraicClosure K/K))
    (hθ : ∀ g : Gal(AlgebraicClosure K/K), PadicInt.toZModPow 1 (θ g : PadicInt p) = 1) :
    FormalHilbert90 θ := by
  let e := ValuationTheory.Completion.separableClosureAutContinuousEquiv K
  let θs : Orientation p Gal(SeparableClosure K/K) :=
    θ.comp (e.symm : Gal(SeparableClosure K/K) →ₜ* Gal(AlgebraicClosure K/K))
  have hs : FormalHilbert90 θs :=
    formalHilbert90_galois_of_charP p K (SeparableClosure K) θs
      (fun g => hθ (e.symm g))
  have h := formalHilbert90_comp_continuousMulEquiv θs e hs
  have heq : θs.comp (e : Gal(AlgebraicClosure K/K) →ₜ* Gal(SeparableClosure K/K)) = θ := by
    apply ContinuousMonoidHom.ext
    intro g
    change θ (e.symm (e g)) = θ g
    exact congrArg θ (e.symm_apply_apply g)
  rw [heq] at h
  exact h

end Yamaguchi26AbfaithfulGalois
