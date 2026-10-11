/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.Completions.Conditional.SamePrimeExponentUnit
import EtaleFundamentalGroups.Kummer.Completions.MaximalAdic.RegularPairNoetherian
import EtaleFundamentalGroups.Kummer.LocalGeometry.HeightTwo.PrimeRootCover
import EtaleFundamentalGroups.Kummer.SelectedRoot.Intermediate.ExponentUnit

/-!
# A one-root same-prime completion terminal

This is the application-shaped one-variable specialization of the literal
same-prime completion theorem.  A prime parameter with regular quotient in a
two-dimensional regular local ring is completed at the closed point.  The
regular pair containing that parameter supplies all domain and prime
preservation facts needed by the completed obstruction.

Thus a finite-etale exact-root factor, one closed prime, and its primitive
Away map are the only data left to the geometric producer.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing

universe uA uE

/-- A literal finite-etale factor over the one-root cover forces the root
exponent to be a unit in the original two-dimensional base.

All completion geometry is produced from the prime parameter and regularity
of its quotient.  The same closed prime `p` is retained through the
faithfully-flat Henselian pushout by the imported same-prime theorem. -/
theorem exponent_isUnit_of_oneRoot_samePrime_completion
    {A : Type uA} [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    {N : ℕ} (hN : 0 < N) {y : A} (hy : Prime y)
    (hyQuot : IsRegularLocalRing (A ⧸ Ideal.span ({y} : Set A)))
    (hdim : ringKrullDim A = ((2 : ℕ∞) : WithBot ℕ∞))
    (hCharZero : CharZero (A ⧸ Ideal.span ({y} : Set A)))
    {E : Type uE} [CommRing E]
    [Algebra
      (iteratedRadical A 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) E]
    [Algebra A E]
    [IsScalarTower A
      (iteratedRadical A 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) E]
    [Module.Finite
      (iteratedRadical A 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) E]
    [Algebra.Etale
      (iteratedRadical A 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) E]
    (p : Ideal E) [p.IsMaximal]
    [hpOver :
      letI : IsLocalRing
          (iteratedRadical A 1
            (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) :=
        isLocalRing_iteratedRadical
          (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)
          (fun _ ↦ hN) (fun _ ↦ by
            rw [mem_maximalIdeal]
            exact hy.not_isUnit)
      p.LiesOver
        (maximalIdeal
          (iteratedRadical A 1
            (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)))]
    (hAway :
      (Localization.awayMap
        (algebraMap A (Localization.AtPrime p)) y).Etale) :
    IsUnit (N : A) := by
  obtain ⟨z, hreg, hgen⟩ :=
    exists_regular_pair_of_prime_regular_quotient_dimension_two
      hy hyQuot hdim
  let n : Fin 1 → ℕ := fun _ ↦ N
  let a : Fin 1 → A := fun _ ↦ y
  let s : Fin 1 → A := fun _ ↦ y
  have hn : ∀ i, 0 < n i := by
    intro i
    simpa [n] using hN
  have hstage : ∀ i, a i ∈ maximalIdeal A ∨ n i = 1 := by
    intro i
    left
    rw [mem_maximalIdeal]
    simpa [a] using hy.not_isUnit
  let : IsLocalRing (iteratedRadical A 1 n a) :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
  have hsPrimeOrUnit : ∀ i, Prime (s i) ∨ IsUnit (s i) := by
    intro i
    exact Or.inl (by simpa [s] using hy)
  have hCharZeroS : ∀ i, Prime (s i) →
      CharZero (A ⧸ Ideal.span {s i}) := by
    intro i _
    simpa [s] using hCharZero
  have hAssoc : Associated y (∏ i, s i) := by
    simp [s]
  have hcompletion :=
    maximalAdicCompletion_regularPair_geometry hreg hgen
  have hall :=
    all_exponents_isUnit_of_conditionalIteratedRadical_samePrime_completion
      (A := A) n a hn hstage s hsPrimeOrUnit hCharZeroS
        y hAssoc hcompletion.1
        (maximalAdicCompletion_isNoetherianRing_of_regularPair hreg hgen)
        (fun i _ ↦ by simpa [s] using hcompletion.2.2.2.1)
        (E := E) p hAway
  simpa [n] using hall (0 : Fin 1)

/-- The same terminal with the exact root cover presented as an ordinary
`AdjoinRoot`.

The canonical equivalence from the one-stage recursive radical transports
finiteness, etaleness, and the literal closed prime.  In particular, callers
which obtained their global finite-etale factor from purity over
`AdjoinRoot (X ^ N - C y)` do not have to expose any comparison between two
independently chosen factors. -/
theorem exponent_isUnit_of_adjoinRoot_samePrime_completion
    {A : Type uA} [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    {N : ℕ} (hN : 0 < N) {y : A} (hy : Prime y)
    (hyQuot : IsRegularLocalRing (A ⧸ Ideal.span ({y} : Set A)))
    (hdim : ringKrullDim A = ((2 : ℕ∞) : WithBot ℕ∞))
    (hCharZero : CharZero (A ⧸ Ideal.span ({y} : Set A)))
    {E : Type uE} [CommRing E]
    [Algebra (AdjoinRoot (Polynomial.X ^ N - Polynomial.C y)) E]
    [Algebra A E]
    [IsScalarTower A
      (AdjoinRoot (Polynomial.X ^ N - Polynomial.C y)) E]
    [Module.Finite (AdjoinRoot (Polynomial.X ^ N - Polynomial.C y)) E]
    [Algebra.Etale (AdjoinRoot (Polynomial.X ^ N - Polynomial.C y)) E]
    [IsLocalRing (AdjoinRoot (Polynomial.X ^ N - Polynomial.C y))]
    (p : Ideal E) [p.IsMaximal]
    [p.LiesOver
      (maximalIdeal
        (AdjoinRoot (Polynomial.X ^ N - Polynomial.C y)))]
    (hAway :
      (Localization.awayMap
        (algebraMap A (Localization.AtPrime p)) y).Etale) :
    IsUnit (N : A) := by
  let n : Fin 1 → ℕ := fun _ ↦ N
  let a : Fin 1 → A := fun _ ↦ y
  let B := iteratedRadical A 1 n a
  let D := AdjoinRoot (Polynomial.X ^ N - Polynomial.C y)
  have hn : ∀ i, 0 < n i := by
    intro i
    simpa [n] using hN
  have ha : ∀ i, a i ∈ maximalIdeal A := by
    intro i
    rw [mem_maximalIdeal]
    simpa [a] using hy.not_isUnit
  let : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
  let e : B ≃ₐ[A] D := by
    simpa only [B, D, n, a] using oneIteratedRadicalAlgEquiv A N y
  let bDAlgebra : Algebra B D := e.toRingEquiv.toRingHom.toAlgebra
  let : Algebra B D := bDAlgebra
  let : IsScalarTower A B D :=
    IsScalarTower.of_algebraMap_eq fun z ↦ (e.commutes z).symm
  let bEAlgebra : Algebra B E :=
    ((algebraMap D E).comp (algebraMap B D)).toAlgebra
  let : Algebra B E := bEAlgebra
  let : IsScalarTower B D E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A B E := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    calc
      algebraMap A E z = algebraMap D E (algebraMap A D z) :=
        IsScalarTower.algebraMap_apply A D E z
      _ = algebraMap D E (algebraMap B D (algebraMap A B z)) := by
        rw [← IsScalarTower.algebraMap_apply A B D]
      _ = algebraMap B E (algebraMap A B z) := rfl
  let eB : B ≃ₐ[B] D :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun _ ↦ rfl)
  let : Module.Finite B D :=
    Module.Finite.of_surjective eB.toLinearMap eB.surjective
  let : Module.Finite B E := Module.Finite.trans D E
  let : Algebra.Etale B D := Algebra.Etale.of_equiv eB
  let : Algebra.Etale B E := Algebra.Etale.comp B D E
  let : IsLocalHom (algebraMap B D) :=
    IsLocalHom.of_surjective (algebraMap B D) e.surjective
  let : (maximalIdeal D).LiesOver (maximalIdeal B) :=
    Ideal.LiesOver.mk
      (IsLocalRing.maximalIdeal_comap (algebraMap B D)).symm
  let : p.LiesOver (maximalIdeal B) :=
    Ideal.LiesOver.trans p (maximalIdeal D) (maximalIdeal B)
  exact
    exponent_isUnit_of_oneRoot_samePrime_completion
      (A := A) hN hy hyQuot hdim hCharZero (E := E) p hAway

end EtaleFundamentalGroups.Kummer

end
