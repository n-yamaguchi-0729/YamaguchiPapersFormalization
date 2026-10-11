/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.Algebra.PrimeRigidity
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Tactic.Ring

/-!
# Trivial intrinsic inertia on an unramified domain

The literal coefficient automorphisms in ideal inertia agree modulo the
prime. Prime rigidity proves equality on the original domain itself, so
the intrinsic inertia group has at most one element.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- Actual coefficient-automorphism inertia is trivial on an unramified
domain. Neither the acting automorphism group nor the base needs to be finite. -/
theorem commAlgIdealInertia_subsingleton_of_unramified
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) [IsDomain B.carrier]
    [Algebra.FormallyUnramified A B.carrier] [Algebra.EssFiniteType A B.carrier]
    (Q : Ideal B.carrier) [Q.IsPrime] :
    Subsingleton (commAlgIdealInertiaGroup A B Q).carrier := by
  constructor
  intro σ τ
  have hmaps : σ.val.toAlgHom = τ.val.toAlgHom := by
    apply Algebra.FormallyUnramified.algHom_ext_of_sub_mem_prime (R := A) Q
    intro b
    have hσ : σ.val b - b ∈ Q := Ideal.mem_inertia.mp σ.property b
    have hτ : τ.val b - b ∈ Q := Ideal.mem_inertia.mp τ.property b
    change σ.val b - τ.val b ∈ Q
    have hsub : σ.val b - τ.val b = (σ.val b - b) - (τ.val b - b) := by ring
    rw [hsub]
    exact Q.sub_mem hσ hτ
  apply Subtype.ext
  apply AlgEquiv.ext
  intro b
  exact AlgHom.congr_fun hmaps b

end EtaleFundamentalGroups.Inertia
