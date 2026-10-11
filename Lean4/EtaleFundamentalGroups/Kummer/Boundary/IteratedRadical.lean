/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.IteratedRadical.Basic
import EtaleFundamentalGroups.Kummer.Descent.MultiAwayUnitDescent

/-!
# Iterated Kummer exponents on a full boundary complement

Formal unramifiedness of an iterated Kummer radical on the complement of a
finite boundary makes every exponent a unit on that complement.  Prime
multi-boundary unit descent then reflects all of those units to the original
domain.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped BigOperators

universe u v

/--
Every exponent of a formally unramified iterated Kummer radical on a full
prime-boundary complement is already a unit in the original domain.
-/
theorem all_exponents_isUnit_of_formallyUnramified_boundaryIteratedRadical
    {R : Type u} {S : Type v} [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S]
    {r : ℕ} (t : Fin r → R)
    [IsLocalization.Away
      (∏ i ∈ (Finset.univ : Finset (Fin r)), t i) S]
    (ht : ∀ i, Prime (t i))
    (hCharZero : ∀ i, CharZero (R ⧸ Ideal.span {t i}))
    (n : Fin r → ℕ) (hn : ∀ i, 0 < n i)
    [Algebra.FormallyUnramified S
      (iteratedRadical S r n (fun i ↦ algebraMap R S (t i)))] :
    ∀ i, IsUnit (n i : R) := by
  have hBoundary_ne :
      (∏ i ∈ (Finset.univ : Finset (Fin r)), t i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ (ht i).ne_zero
  let : IsDomain S :=
    IsLocalization.Away.isDomain S hBoundary_ne
  have hnS : ∀ i, IsUnit (n i : S) :=
    all_exponents_isUnit_of_formallyUnramified_iteratedRadical
      (A := S) n (fun i ↦ algebraMap R S (t i)) hn
  intro i
  exact
    isUnit_natCast_of_isUnit_algebraMap_away_finsetProduct
      (R := R) (S := S) Finset.univ t
      (fun j _ ↦ ht j) (fun j _ ↦ hCharZero j) (hn i) (by
        simpa using hnS i)

end EtaleFundamentalGroups.Kummer
