/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Completions.Conditional.SamePrimeGlobalBoundaryAway

/-!
# Exact-root completion terminal without a public closed prime

A finite algebra over the local exact-root cover has a maximal ideal over the
closed point by lying over.  This file chooses that ideal internally and feeds
the resulting literal prime to the global-Away same-prime completion terminal.

Thus a caller which has produced one global finite-etale normalization factor
and its primitive Away map need not expose a comparison with an independently
chosen completed factor or a closed-prime parameter.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing

universe uA uE

/-- A global finite-etale factor of the one-root cover, together with its
literal primitive Away map, forces the root exponent to be a unit.

The closed prime is produced from module-finiteness and is then tracked by
the same-prime completion theorem.  No prime comparison, component
bijection, or degree equality is a public hypothesis. -/
theorem
    exponent_isUnit_of_adjoinRoot_global_finiteEtale_boundaryAway
    {A : Type uA} [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    {N : ℕ} (hN : 0 < N) {y : A} (hy : Prime y)
    (hyQuot : IsRegularLocalRing (A ⧸ Ideal.span ({y} : Set A)))
    (hdim : ringKrullDim A = ((2 : ℕ∞) : WithBot ℕ∞))
    (hCharZero : CharZero (A ⧸ Ideal.span ({y} : Set A)))
    {E : Type uE} [CommRing E] [Nontrivial E]
    [Algebra
      (AdjoinRoot (Polynomial.X ^ N - Polynomial.C y)) E]
    [Algebra A E]
    [IsScalarTower A
      (AdjoinRoot (Polynomial.X ^ N - Polynomial.C y)) E]
    [Module.Finite
      (AdjoinRoot (Polynomial.X ^ N - Polynomial.C y)) E]
    [Algebra.Etale
      (AdjoinRoot (Polynomial.X ^ N - Polynomial.C y)) E]
    [IsLocalRing
      (AdjoinRoot (Polynomial.X ^ N - Polynomial.C y))]
    (hAway : (Localization.awayMap (algebraMap A E) y).Etale) :
    IsUnit (N : A) := by
  let D := AdjoinRoot (Polynomial.X ^ N - Polynomial.C y)
  let : Algebra.IsIntegral D E := Algebra.IsIntegral.of_finite D E
  have hker : RingHom.ker (algebraMap D E) ≤ maximalIdeal D :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (algebraMap D E))
  obtain ⟨p, hpMax, hpUnder⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (maximalIdeal D) hker
  let : p.IsMaximal := hpMax
  let : p.LiesOver (maximalIdeal D) :=
    (Ideal.liesOver_iff p (maximalIdeal D)).mpr hpUnder.symm
  exact
    exponent_isUnit_of_adjoinRoot_samePrime_global_completion
      (A := A) hN hy hyQuot hdim hCharZero (E := E) p hAway

end EtaleFundamentalGroups.Kummer

end
