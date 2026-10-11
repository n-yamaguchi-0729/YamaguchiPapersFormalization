/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.IntegralBase.ChosenLocalization.Core

/-!
# Existence of a chosen local normalization factor

For a finite integral enlargement `A → B` with `B` Henselian local, a prime
of the common normalization over the closed point exists by integrality.  The
chosen-localization theorem then makes its localization finite etale over `B`,
with a unique closed prime, while retaining the literal primitive `A`-away
map.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing

universe uA uB uL

/-- The common normalization has a chosen local factor over the closed point
of the integral Henselian base.  The prime is produced internally by lying
over; finiteness, etaleness, closed-prime uniqueness, and the primitive away
property are then supplied by
`integralClosure_integralBase_chosenLocalization_finiteEtale_unique_away`.
-/
theorem
    exists_integralClosure_integralBase_chosenLocalization_finiteEtale_unique_away
    {A : Type uA} {B : Type uB} {L : Type uL}
    [CommRing A] [CommRing B] [Field L]
    [IsNoetherianRing A]
    [HenselianLocalRing B]
    [Algebra A B] [Module.Finite A B]
    [Algebra A L] [Algebra B L] [IsScalarTower A B L]
    (hEtale : Algebra.Etale B (integralClosure B L))
    (f : A)
    (hAway :
      (Localization.awayMap
        (algebraMap A (integralClosure A L)) f).Etale) :
    let C := integralClosure A L
    letI : Algebra B C := integralClosureIntegralBaseAlgebra
    letI : IsScalarTower A B C :=
      integralClosureIntegralBase_isScalarTower
    ∃ (q : Ideal C) (_ : q.IsPrime)
      (_ : q.LiesOver (maximalIdeal B)),
      let D := Localization.AtPrime q
      Module.Finite B D ∧
        Algebra.Etale B D ∧
        (maximalIdeal D).LiesOver (maximalIdeal B) ∧
        (∀ Q : Ideal D, Q.IsPrime →
          Q.LiesOver (maximalIdeal B) → Q = maximalIdeal D) ∧
        @Algebra.Etale
          (Localization.Away f)
          (Localization.Away (algebraMap A D f))
          _ _
          (Localization.awayMap (algebraMap A D) f).toAlgebra := by
  dsimp only
  let C := integralClosure A L
  let : Algebra B C := integralClosureIntegralBaseAlgebra
  let : IsScalarTower A B C :=
    integralClosureIntegralBase_isScalarTower
  let : Algebra.IsIntegral A C :=
    IsIntegralClosure.isIntegral_algebra A L
  let : Algebra.IsIntegral B C :=
    Algebra.IsIntegral.tower_top A
  have hker : RingHom.ker (algebraMap B C) ≤ maximalIdeal B :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (algebraMap B C))
  obtain ⟨q, hqMaximal, hqComap⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (maximalIdeal B) hker
  let : q.IsPrime := hqMaximal.isPrime
  let : q.LiesOver (maximalIdeal B) :=
    (Ideal.liesOver_iff q (maximalIdeal B)).mpr hqComap.symm
  exact ⟨q, inferInstance, inferInstance,
    integralClosure_integralBase_chosenLocalization_finiteEtale_unique_away
      (A := A) (B := B) (L := L) hEtale f hAway q⟩

end EtaleFundamentalGroups

end
