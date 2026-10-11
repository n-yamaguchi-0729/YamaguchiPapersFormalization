/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Completions.ChosenFactor.ExponentUnit.BoundaryAway
import Nyll.EtaleFundamentalGroups.Kummer.IteratedRadical.ExponentUnit.IntegralClosurePrimeOrUnit

/-!
# Complete chosen factors with prime-or-unit boundaries

After localizing a normal-crossings chart at a height-two point, boundary
parameters outside that point are units.  This leaf combines the chosen
finite-etale factor construction with the prime-or-unit terminal, so those
inactive boundary factors need not be removed or reindexed before
completion.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing
open scoped BigOperators

universe uA uD

private theorem isLocalRing_of_unique_prime_over_maximal_primeOrUnit
    {R : Type uA} {S : Type uD}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [Module.Finite R S]
    (q : Ideal S) [q.IsPrime]
    [q.LiesOver (maximalIdeal R)]
    (hunique : ∀ Q : Ideal S, Q.IsPrime →
      Q.LiesOver (maximalIdeal R) → Q = q) :
    IsLocalRing S := by
  let : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hqMaximal : q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) q <| by
        rw [← q.over_def (maximalIdeal R)]
        exact IsLocalRing.maximalIdeal.isMaximal R
  refine IsLocalRing.of_unique_max_ideal ⟨q, hqMaximal, ?_⟩
  intro Q hQMaximal
  let : Q.IsPrime := hQMaximal.isPrime
  have hQUnderMaximal : (Q.under R).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R S)
      (fun x ↦ Algebra.IsIntegral.isIntegral x) Q
  have hQOver : Q.LiesOver (maximalIdeal R) :=
    { over := (IsLocalRing.eq_maximalIdeal hQUnderMaximal).symm }
  exact hunique Q inferInstance hQOver

private theorem isLocalHom_of_unique_prime_over_maximal_primeOrUnit
    {R : Type uA} {S : Type uD}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [Module.Finite R S]
    (q : Ideal S) [q.IsPrime]
    [q.LiesOver (maximalIdeal R)]
    (hunique : ∀ Q : Ideal S, Q.IsPrime →
      Q.LiesOver (maximalIdeal R) → Q = q) :
    letI : IsLocalRing S :=
      isLocalRing_of_unique_prime_over_maximal_primeOrUnit q hunique
    IsLocalHom (algebraMap R S) := by
  let : IsLocalRing S :=
    isLocalRing_of_unique_prime_over_maximal_primeOrUnit q hunique
  let : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hqMaximal : q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) q <| by
        rw [← q.over_def (maximalIdeal R)]
        exact IsLocalRing.maximalIdeal.isMaximal R
  have hqEq : q = maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal hqMaximal
  have hcomap :
      (maximalIdeal S).comap (algebraMap R S) = maximalIdeal R := by
    rw [← hqEq]
    exact (q.over_def (maximalIdeal R)).symm
  exact ((IsLocalRing.local_hom_TFAE (algebraMap R S)).out 5 1).mp hcomap

private theorem faithfullyFlat_of_unique_prime_over_maximal_primeOrUnit
    {R : Type uA} {S : Type uD}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [Module.Finite R S] [Algebra.Etale R S]
    (q : Ideal S) [q.IsPrime]
    [q.LiesOver (maximalIdeal R)]
    (hunique : ∀ Q : Ideal S, Q.IsPrime →
      Q.LiesOver (maximalIdeal R) → Q = q) :
    letI : IsLocalRing S :=
      isLocalRing_of_unique_prime_over_maximal_primeOrUnit q hunique
    Module.FaithfullyFlat R S := by
  let : IsLocalRing S :=
    isLocalRing_of_unique_prime_over_maximal_primeOrUnit q hunique
  let : IsLocalHom (algebraMap R S) :=
    isLocalHom_of_unique_prime_over_maximal_primeOrUnit q hunique
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- A finite etale factor uniquely selected over the closed point detects
all positive radical exponents when the independent Away boundary consists
of prime or unit factors. -/
theorem all_exponents_isUnit_of_completeChosenFactor_boundaryAway_primeOrUnit_universe
    {A : Type uA} [CommRing A] [IsDomain A] [IsLocalRing A]
    {r b : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i, a i ∈ maximalIdeal A ∨ n i = 1)
    (s : Fin b → A)
    (hsPrimeOrUnit : ∀ i, Prime (s i) ∨ IsUnit (s i))
    (hCharZero : ∀ i, Prime (s i) →
      CharZero (A ⧸ Ideal.span {s i}))
    (f : A) (hAssoc : Associated f (∏ i, s i)) :
    let B := iteratedRadical A r n a
    letI : IsLocalRing B :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
    ∀ {D : Type uD} [CommRing D] [Algebra B D]
      [Algebra A D] [IsScalarTower A B D]
      [Module.Finite B D] [Algebra.Etale B D],
      ∀ (q : Ideal D) [q.IsPrime]
        [q.LiesOver (maximalIdeal B)],
        (∀ Q : Ideal D, Q.IsPrime →
          Q.LiesOver (maximalIdeal B) → Q = q) →
        (Localization.awayMap (algebraMap A D) f).Etale →
        ∀ i, IsUnit (n i : A) := by
  dsimp only
  intro D _ _ _ _ _ _ q _ _ hunique hAway
  let B := iteratedRadical A r n a
  let : IsLocalRing B :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
  let : IsLocalRing D :=
    isLocalRing_of_unique_prime_over_maximal_primeOrUnit q hunique
  let : IsLocalHom (algebraMap B D) :=
    isLocalHom_of_unique_prime_over_maximal_primeOrUnit q hunique
  let : Module.FaithfullyFlat B D :=
    faithfullyFlat_of_unique_prime_over_maximal_primeOrUnit q hunique
  exact
    all_exponents_isUnit_of_iteratedRadical_formallyEtaleFactor_boundaryAway_primeOrUnit_universe
      (A := A) n a hn s hsPrimeOrUnit hCharZero
        f hAssoc (D := D) hAway

end EtaleFundamentalGroups.Kummer

end
