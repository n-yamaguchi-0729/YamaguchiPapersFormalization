/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.Main

/-!
# Finite-separable normalization inertia

For a noetherian normal domain, the integral closure in a finite separable
extension of its fraction field is finite.  This supplies the finiteness input
needed by the split normal-crossings inertia theorem without a Nagata or an
arithmetic finite-type hypothesis.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe u uk

/-- Over an integrally closed regular local domain, normalization inertia
along a component of a split strict-normal-crossings boundary has order prime
to every prime residue characteristic reached from that component.

The normalization is finite because a regular ring is noetherian and the
generic extension is finite separable. -/
theorem splitStrictNormalCrossings_normalizationInertia_coprime_of_isIntegrallyClosed
    {A K L : Type u} {k : Type uk}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [IsIntegrallyClosed A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    [CommRing k] [Nontrivial k]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (hCharZero : ∀ j, j.1 < r →
      CharZero (A ⧸ Ideal.span ({t j} : Set A)))
    (hAwayBase : (Localization.awayMap
      (algebraMap A (integralClosure A L)) f).Etale)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span ({t i} : Set A))]
    (phi : (A ⧸ Ideal.span ({t i} : Set A)) →+* k)
    (p : ℕ) [CharP k p] (hp : p.Prime) :
    Nat.Coprime
      (Nat.card (Q.toAddSubgroup.inertia Gal(L/K))) p := by
  let : Module.Finite A (integralClosure A L) :=
    IsIntegralClosure.finite A K L (integralClosure A L)
  exact
    splitStrictNormalCrossings_normalizationInertia_coprime
      (K := K) (L := L) hNC i hi hCharZero hAwayBase Q phi p hp

end EtaleFundamentalGroups.Kummer

end
