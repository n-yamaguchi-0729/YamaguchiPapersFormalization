/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.IteratedRadical.ExponentUnit.IntegralClosurePrimeOrUnit

/-!
# The last exponent of a nested iterated radical is a unit

The full root cover used by the height-two strict-normal-crossings argument is
presented as an iterated radical followed by one final `AdjoinRoot`.  This file
exposes the last-coordinate consequence of the prime-or-unit boundary terminal
without adding a comparison hypothesis between that nested presentation and an
iterated radical indexed by `Fin (r + 1)`.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open scoped BigOperators

universe uA uL

/-- If the normalization of a nested full radical cover is etale and its
composite map from the original base is etale away from a prime-or-unit
boundary, then the exponent of the final root is a unit in the original base.

The full exponent and radicand families are constructed internally with
`Fin.snoc`.  The nested `AdjoinRoot` is identified with the corresponding last
stage of `iteratedRadical`, so no presentation equivalence is an input. -/
theorem
    lastExponent_isUnit_of_iteratedRadical_integralClosure_etale_boundaryAway_primeOrUnit_universe
    {A : Type uA} [CommRing A] [IsDomain A]
    {r b : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (N : ℕ) (hN : 0 < N) (y : A)
    (s : Fin b → A)
    (hsPrimeOrUnit : ∀ i, Prime (s i) ∨ IsUnit (s i))
    (hCharZero : ∀ i, Prime (s i) →
      CharZero (A ⧸ Ideal.span {s i}))
    (f : A) (hAssoc : Associated f (∏ i, s i)) :
    let B := iteratedRadical A r n a
    let D := AdjoinRoot (X ^ N - C (algebraMap A B y))
    ∀ {L : Type uL} [Field L] [Algebra D L] [FaithfulSMul D L],
      (hEtale : Algebra.Etale D (integralClosure D L)) →
      (hAway : (Localization.awayMap
        ((algebraMap D (integralClosure D L)).comp
          ((algebraMap B D).comp (algebraMap A B))) f).Etale) →
      IsUnit (N : A) := by
  dsimp only
  intro L _ _ _ hEtale hAway
  let B := iteratedRadical A r n a
  let D := AdjoinRoot (X ^ N - C (algebraMap A B y))
  let nFull : Fin (r + 1) → ℕ := Fin.snoc n N
  let aFull : Fin (r + 1) → A := Fin.snoc a y
  have hnInit : Fin.init nFull = n := by
    exact @Fin.init_snoc r (fun _ : Fin (r + 1) ↦ ℕ) N n
  have haInit : Fin.init aFull = a := by
    exact @Fin.init_snoc r (fun _ : Fin (r + 1) ↦ A) y a
  have hnLast : nFull (Fin.last r) = N := by
    exact @Fin.snoc_last r (fun _ : Fin (r + 1) ↦ ℕ) N n
  have haLast : aFull (Fin.last r) = y := by
    exact @Fin.snoc_last r (fun _ : Fin (r + 1) ↦ A) y a
  let Full := iteratedRadical A (r + 1) nFull aFull
  let Dcat : CommAlgCat A := CommAlgCat.of A D
  have hFullD : Full = Dcat := by
    change iteratedRadical A (r + 1) nFull aFull = CommAlgCat.of A D
    unfold iteratedRadical
    dsimp only
    rw [hnInit, haInit, hnLast, haLast]
  have hnFull : ∀ i, 0 < nFull i := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [hnLast] using hN
    · simpa [nFull] using hn j
  have hTerminalFull :
      ∀ {K : Type uL} [Field K] [Algebra Full K]
        [FaithfulSMul Full K],
        Algebra.Etale Full (integralClosure Full K) →
        (Localization.awayMap
          ((algebraMap Full (integralClosure Full K)).comp
            (algebraMap A Full)) f).Etale →
        ∀ i, IsUnit (nFull i : A) := by
    exact
      (
all_exponents_isUnit_of_iteratedRadical_integralClosure_etale_boundaryAway_primeOrUnit_universe
        (A := A) nFull aFull hnFull s hsPrimeOrUnit hCharZero f hAssoc)
  rw [hFullD] at hTerminalFull
  have hAll : ∀ i, IsUnit (nFull i : A) := by
    apply hTerminalFull (K := L)
    · change Algebra.Etale D (integralClosure D L)
      exact hEtale
    · change (Localization.awayMap
        ((algebraMap D (integralClosure D L)).comp
          (algebraMap A D)) f).Etale
      change (Localization.awayMap
        ((algebraMap D (integralClosure D L)).comp
          ((algebraMap B D).comp (algebraMap A B))) f).Etale
      exact hAway
  simpa [hnLast] using hAll (Fin.last r)

end EtaleFundamentalGroups.Kummer

end
