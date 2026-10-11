/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.LocalGeometry.HeightTwo.NonunitLocalization

/-!
# Globalizing an integer unit from height-two localizations

For a prime divisor in a Noetherian local domain, failure of an integer to
be a unit on the divisor is detected at a height-two localization.  Thus a
unit result at every such localization globalizes to the generic point of
the divisor.
-/

namespace EtaleFundamentalGroups

universe u

/-- If a positive integer is a unit at every height-two localization lying
strictly above a prime parameter, then it is already a unit modulo that
parameter. -/
theorem isUnit_natCast_mod_prime_of_heightTwo_localizations
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A]
    (t : A) (ht : Prime t) (e : ℕ) (he : 0 < e)
    [CharZero (A ⧸ Ideal.span {t})]
    (hlocal : ∀ (P : Ideal A) [P.IsPrime],
      Ideal.span {t} < P → P.height = 2 →
        IsUnit (algebraMap A (Localization.AtPrime P) (e : A))) :
    IsUnit (e : A ⧸ Ideal.span {t}) := by
  by_contra he_nonunit
  obtain ⟨P, hP, -, hstrict, hheight, he_local_nonunit⟩ :=
    exists_heightTwo_prime_of_nonunit_natCast_mod_prime
      t ht e he he_nonunit
  let : P.IsPrime := hP
  exact he_local_nonunit (hlocal P hstrict hheight)

end EtaleFundamentalGroups
